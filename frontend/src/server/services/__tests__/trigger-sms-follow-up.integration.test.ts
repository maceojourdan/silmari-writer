/**
 * trigger-sms-follow-up.integration.test.ts - Terminal Condition / Full Path
 *
 * Exercises the complete path from finalize event to terminal success:
 * 1. Detect finalize completion event (smsOptIn=true, valid phone)
 * 2. Load answer and contact data from DAOs
 * 3. Compose SMS follow-up message
 * 4. Send SMS via external provider (spied/mocked)
 * 5. Record SMS dispatch result
 *
 * TLA+ Properties:
 * - Reachability: trigger (handleFinalizeEvent) → terminal condition ({ status: 'completed' })
 * - TypeInvariant: types consistent across all step boundaries
 * - ErrorConsistency: all error branches emit structured SmsErrors
 *
 * Resource: db-h2s4 (service)
 * Path: 335-trigger-sms-follow-up-on-answer-finalization
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import type { FinalizeEvent } from '@/server/data_structures/FinalizeEvent';

// ---------------------------------------------------------------------------
// Mock ALL external dependencies
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/AnswerDAO', () => ({
  AnswerDAO: { findById: vi.fn() },
}));

vi.mock('../../data_access_objects/UserDAO', () => ({
  UserDAO: { findById: vi.fn() },
}));

vi.mock('../../data_access_objects/SmsFollowUpDAO', () => ({
  SmsFollowUpDAO: { insert: vi.fn() },
}));

vi.mock('@/server/logging/smsLogger', () => ({
  smsLogger: { info: vi.fn(), warn: vi.fn(), error: vi.fn(), critical: vi.fn() },
}));

// ---------------------------------------------------------------------------
// Imports (must come after vi.mock)
// ---------------------------------------------------------------------------

import { TriggerSmsFollowUpService } from '../TriggerSmsFollowUpService';
import { AnswerDAO } from '../../data_access_objects/AnswerDAO';
import { UserDAO } from '../../data_access_objects/UserDAO';
import { SmsFollowUpDAO } from '../../data_access_objects/SmsFollowUpDAO';
import { smsLogger } from '@/server/logging/smsLogger';

const mockAnswerDAO = vi.mocked(AnswerDAO);
const mockUserDAO = vi.mocked(UserDAO);
const mockSmsFollowUpDAO = vi.mocked(SmsFollowUpDAO);
const mockLogger = vi.mocked(smsLogger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const answerId = '550e8400-e29b-41d4-a716-446655440000';
const userId = '660e8400-e29b-41d4-a716-446655440000';

const event: FinalizeEvent = {
  answerId,
  userId,
  smsOptIn: true,
  phoneNumber: '+15551234567',
};

const validAnswer = {
  id: answerId,
  status: 'FINALIZED' as const,
  finalized: true,
  editable: false,
  locked: false,
  content: 'My finalized answer',
  userId,
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const validUser = {
  id: userId,
  smsOptIn: true,
  phoneNumber: '+15551234567',
  createdAt: '2026-02-28T12:00:00.000Z',
  updatedAt: '2026-02-28T12:00:00.000Z',
};

const storedRecord = {
  id: '770e8400-e29b-41d4-a716-446655440000',
  answerId,
  phoneNumber: '+15551234567',
  message: expect.any(String),
  status: 'sent',
  messageId: 'SM-integration-123',
  createdAt: expect.any(String),
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('TriggerSmsFollowUpService — Integration: Full Path Exercise', () => {
  let sendSmsSpy: ReturnType<typeof vi.spyOn>;

  beforeEach(() => {
    vi.clearAllMocks();
    vi.restoreAllMocks();
  });

  // -------------------------------------------------------------------------
  // Reachability: trigger → terminal success
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should complete the full path from finalize event to terminal success', async () => {
      // Arrange: wire up all mock DAOs
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(validUser);
      mockSmsFollowUpDAO.insert.mockResolvedValue(storedRecord as any);

      // Spy on sendSms to intercept the external provider call
      sendSmsSpy = vi.spyOn(TriggerSmsFollowUpService, 'sendSms')
        .mockResolvedValue({ status: 'sent', messageId: 'SM-integration-123' });

      // Act
      const result = await TriggerSmsFollowUpService.handleFinalizeEvent(event);

      // Assert: terminal state reached
      expect(result).toEqual({ status: 'completed' });

      // Assert: SMS sent exactly once
      expect(sendSmsSpy).toHaveBeenCalledOnce();

      // Assert: SMS follow-up record persisted
      expect(mockSmsFollowUpDAO.insert).toHaveBeenCalledOnce();
      expect(mockSmsFollowUpDAO.insert).toHaveBeenCalledWith(
        expect.objectContaining({
          answerId,
          phoneNumber: '+15551234567',
          status: 'sent',
          messageId: 'SM-integration-123',
        }),
      );

      // Assert: success log emitted
      expect(mockLogger.info).toHaveBeenCalledWith(
        'SMS follow-up record persisted',
        expect.objectContaining({ answerId }),
      );
    });

    it('should complete with no-op when smsOptIn is false', async () => {
      const optOutEvent: FinalizeEvent = { ...event, smsOptIn: false };

      const result = await TriggerSmsFollowUpService.handleFinalizeEvent(optOutEvent);

      expect(result).toEqual({ status: 'completed' });

      // No further steps should execute
      expect(mockAnswerDAO.findById).not.toHaveBeenCalled();
      expect(mockUserDAO.findById).not.toHaveBeenCalled();
      expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant: types consistent across boundaries
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return object with status string "completed"', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(validUser);
      mockSmsFollowUpDAO.insert.mockResolvedValue(storedRecord as any);

      sendSmsSpy = vi.spyOn(TriggerSmsFollowUpService, 'sendSms')
        .mockResolvedValue({ status: 'sent', messageId: 'SM-type-check' });

      const result = await TriggerSmsFollowUpService.handleFinalizeEvent(event);

      expect(result).toHaveProperty('status');
      expect(typeof result.status).toBe('string');
      expect(result.status).toBe('completed');
    });

    it('should pass correctly typed payload between load and compose steps', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(validUser);
      mockSmsFollowUpDAO.insert.mockResolvedValue(storedRecord as any);

      sendSmsSpy = vi.spyOn(TriggerSmsFollowUpService, 'sendSms')
        .mockResolvedValue({ status: 'sent', messageId: 'SM-payload-check' });

      await TriggerSmsFollowUpService.handleFinalizeEvent(event);

      // sendSms should receive a string message and phone number
      expect(sendSmsSpy).toHaveBeenCalledWith(
        expect.any(String),
        '+15551234567',
      );

      // The message should include the answer summary
      const calledMessage = sendSmsSpy.mock.calls[0][0] as string;
      expect(calledMessage.length).toBeLessThanOrEqual(160);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency: structured errors across all boundaries
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should propagate ANSWER_NOT_FOUND when AnswerDAO returns null', async () => {
      mockAnswerDAO.findById.mockResolvedValue(null);

      try {
        await TriggerSmsFollowUpService.handleFinalizeEvent(event);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('ANSWER_NOT_FOUND');
        expect(e.statusCode).toBe(404);
      }

      // Subsequent steps should not execute
      expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
    });

    it('should propagate DATABASE_FAILURE when UserDAO returns null', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(null);

      try {
        await TriggerSmsFollowUpService.handleFinalizeEvent(event);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('DATABASE_FAILURE');
        expect(e.statusCode).toBe(500);
      }

      expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
    });

    it('should propagate PERSISTENCE_FAILURE when SmsFollowUpDAO.insert fails', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(validUser);
      mockSmsFollowUpDAO.insert.mockRejectedValue(new Error('DB write failed'));

      sendSmsSpy = vi.spyOn(TriggerSmsFollowUpService, 'sendSms')
        .mockResolvedValue({ status: 'sent', messageId: 'SM-persist-fail' });

      try {
        await TriggerSmsFollowUpService.handleFinalizeEvent(event);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('PERSISTENCE_FAILURE');
        expect(e.statusCode).toBe(500);
      }

      // SMS was sent, but persistence failed — critical log should be emitted
      expect(mockLogger.critical).toHaveBeenCalledWith(
        'Failed to persist SMS follow-up record',
        expect.any(Error),
        expect.objectContaining({ answerId }),
      );
    });

    it('should propagate PROVIDER_FAILURE when sendSms throws', async () => {
      mockAnswerDAO.findById.mockResolvedValue(validAnswer);
      mockUserDAO.findById.mockResolvedValue(validUser);

      const { SmsFollowUpErrors } = await import('@/server/error_definitions/SmsErrors');
      sendSmsSpy = vi.spyOn(TriggerSmsFollowUpService, 'sendSms')
        .mockRejectedValue(SmsFollowUpErrors.PROVIDER_FAILURE());

      try {
        await TriggerSmsFollowUpService.handleFinalizeEvent(event);
        expect.fail('Should have thrown');
      } catch (e: any) {
        expect(e.code).toBe('PROVIDER_FAILURE');
        expect(e.statusCode).toBe(502);
      }

      // Persistence step should not execute after send failure
      expect(mockSmsFollowUpDAO.insert).not.toHaveBeenCalled();
    });
  });
});
