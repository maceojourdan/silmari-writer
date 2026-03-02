/**
 * PrimaryKpiService.test.ts - Step 3: Process and persist primary KPI action
 *
 * TLA+ Properties:
 * - Reachability: valid DTO -> assert DAO.insert() called -> returns persisted record
 * - TypeInvariant: assert returned object matches PrimaryKpiRecord type via Zod safeParse
 * - ErrorConsistency:
 *     - Invalid business rule -> KpiErrors.DomainValidationError
 *     - DAO throws -> KpiErrors.PersistenceError
 *     - Assert analytics emitter NOT called in both error cases (analyticsEmitted: false)
 *
 * Resource: db-h2s4 (service)
 * Path: 339-record-primary-kpi-analytics-event
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import {
  PrimaryKpiRecordSchema,
  type PrimaryKpiRecord,
  type RecordPrimaryKpiRequest,
} from '@/server/data_structures/PrimaryKpiRecord';
import { KpiError } from '@/server/error_definitions/KpiErrors';

// ---------------------------------------------------------------------------
// Mock DAO
// ---------------------------------------------------------------------------

vi.mock('../../data_access_objects/PrimaryKpiDAO', () => ({
  PrimaryKpiDAO: {
    insert: vi.fn(),
    findById: vi.fn(),
    updateStatus: vi.fn(),
  },
}));

// ---------------------------------------------------------------------------
// Mock Logger
// ---------------------------------------------------------------------------

vi.mock('../../logging/kpiLogger', () => ({
  kpiLogger: {
    info: vi.fn(),
    warn: vi.fn(),
    error: vi.fn(),
    critical: vi.fn(),
  },
}));

import { PrimaryKpiDAO } from '../../data_access_objects/PrimaryKpiDAO';
import { kpiLogger } from '../../logging/kpiLogger';
import { PrimaryKpiService } from '../PrimaryKpiService';

const mockDAO = vi.mocked(PrimaryKpiDAO);
const mockLogger = vi.mocked(kpiLogger);

// ---------------------------------------------------------------------------
// Test Data
// ---------------------------------------------------------------------------

const validRequest: RecordPrimaryKpiRequest = {
  userId: 'user-001',
  actionType: 'purchase',
  metadata: { amount: 99.99, currency: 'USD' },
};

const persistedRecord: PrimaryKpiRecord = {
  id: '550e8400-e29b-41d4-a716-446655440001',
  userId: 'user-001',
  actionType: 'purchase',
  metadata: { amount: 99.99, currency: 'USD' },
  status: 'PERSISTED',
  timestamp: '2026-03-01T14:30:00.000Z',
  createdAt: '2026-03-01T14:30:01.000Z',
};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('PrimaryKpiService.record — Step 3: Process and persist primary KPI action', () => {
  beforeEach(() => {
    vi.clearAllMocks();

    // Default happy-path: DAO insert succeeds and returns persisted record
    mockDAO.insert.mockResolvedValue(persistedRecord);
  });

  // -------------------------------------------------------------------------
  // Reachability
  // -------------------------------------------------------------------------

  describe('Reachability', () => {
    it('should call DAO.insert with the request data when given a valid DTO', async () => {
      const result = await PrimaryKpiService.record(validRequest);

      expect(mockDAO.insert).toHaveBeenCalledTimes(1);
      expect(mockDAO.insert).toHaveBeenCalledWith(
        expect.objectContaining({
          userId: validRequest.userId,
          actionType: validRequest.actionType,
          metadata: validRequest.metadata,
        }),
      );
      expect(result).toBeDefined();
    });

    it('should return the persisted record from DAO.insert', async () => {
      const result = await PrimaryKpiService.record(validRequest);

      expect(result.record).toEqual(persistedRecord);
      expect(result.record.id).toBe('550e8400-e29b-41d4-a716-446655440001');
      expect(result.record.userId).toBe('user-001');
      expect(result.record.actionType).toBe('purchase');
      expect(result.record.status).toBe('PERSISTED');
    });

    it('should return analyticsEmitted as a boolean', async () => {
      const result = await PrimaryKpiService.record(validRequest);

      expect(typeof result.analyticsEmitted).toBe('boolean');
    });

    it('should handle request with empty metadata by defaulting to empty object', async () => {
      const requestWithoutMetadata: RecordPrimaryKpiRequest = {
        userId: 'user-002',
        actionType: 'signup',
      };

      const recordWithoutMetadata: PrimaryKpiRecord = {
        ...persistedRecord,
        userId: 'user-002',
        actionType: 'signup',
        metadata: {},
      };
      mockDAO.insert.mockResolvedValue(recordWithoutMetadata);

      const result = await PrimaryKpiService.record(requestWithoutMetadata);

      expect(mockDAO.insert).toHaveBeenCalledTimes(1);
      expect(result.record.userId).toBe('user-002');
      expect(result.record.actionType).toBe('signup');
    });

    it('should log a success info message after persisting the record', async () => {
      await PrimaryKpiService.record(validRequest);

      expect(mockLogger.info).toHaveBeenCalledWith(
        expect.stringContaining('KPI'),
        expect.objectContaining({
          userId: validRequest.userId,
          actionType: validRequest.actionType,
        }),
      );
    });
  });

  // -------------------------------------------------------------------------
  // TypeInvariant
  // -------------------------------------------------------------------------

  describe('TypeInvariant', () => {
    it('should return a record that passes PrimaryKpiRecordSchema validation', async () => {
      const result = await PrimaryKpiService.record(validRequest);
      const parsed = PrimaryKpiRecordSchema.safeParse(result.record);

      expect(parsed.success).toBe(true);
    });

    it('should return an object with record and analyticsEmitted properties', async () => {
      const result = await PrimaryKpiService.record(validRequest);

      expect(result).toHaveProperty('record');
      expect(result).toHaveProperty('analyticsEmitted');
    });

    it('should return a record with all required PrimaryKpiRecord fields', async () => {
      const result = await PrimaryKpiService.record(validRequest);

      expect(result.record).toHaveProperty('id');
      expect(result.record).toHaveProperty('userId');
      expect(result.record).toHaveProperty('actionType');
      expect(result.record).toHaveProperty('metadata');
      expect(result.record).toHaveProperty('status');
      expect(result.record).toHaveProperty('timestamp');
      expect(result.record).toHaveProperty('createdAt');
    });

    it('should return record with status as a valid PrimaryKpiStatus enum value', async () => {
      const result = await PrimaryKpiService.record(validRequest);
      const validStatuses = ['PENDING', 'PERSISTED', 'ANALYTICS_SENT', 'ANALYTICS_FAILED'];

      expect(validStatuses).toContain(result.record.status);
    });
  });

  // -------------------------------------------------------------------------
  // ErrorConsistency
  // -------------------------------------------------------------------------

  describe('ErrorConsistency', () => {
    it('should throw KpiError with code DOMAIN_VALIDATION_ERROR when userId is empty', async () => {
      const invalidRequest: RecordPrimaryKpiRequest = {
        userId: '',
        actionType: 'purchase',
        metadata: { amount: 99.99 },
      };

      try {
        await PrimaryKpiService.record(invalidRequest);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(KpiError);
        expect((e as KpiError).code).toBe('DOMAIN_VALIDATION_ERROR');
        expect((e as KpiError).statusCode).toBe(422);
      }
    });

    it('should throw KpiError with code DOMAIN_VALIDATION_ERROR when actionType is empty', async () => {
      const invalidRequest: RecordPrimaryKpiRequest = {
        userId: 'user-001',
        actionType: '',
        metadata: { amount: 99.99 },
      };

      try {
        await PrimaryKpiService.record(invalidRequest);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(KpiError);
        expect((e as KpiError).code).toBe('DOMAIN_VALIDATION_ERROR');
        expect((e as KpiError).statusCode).toBe(422);
      }
    });

    it('should NOT call DAO.insert when business rule validation fails', async () => {
      const invalidRequest: RecordPrimaryKpiRequest = {
        userId: '',
        actionType: 'purchase',
      };

      try {
        await PrimaryKpiService.record(invalidRequest);
        expect.fail('Should have thrown');
      } catch {
        // Expected
      }

      expect(mockDAO.insert).not.toHaveBeenCalled();
    });

    it('should NOT set analyticsEmitted to true when business rule validation fails', async () => {
      const invalidRequest: RecordPrimaryKpiRequest = {
        userId: '',
        actionType: 'purchase',
      };

      try {
        await PrimaryKpiService.record(invalidRequest);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(KpiError);
        // No result returned — analytics emitter never called
      }

      expect(mockDAO.updateStatus).not.toHaveBeenCalled();
    });

    it('should throw KpiError with code PERSISTENCE_ERROR when DAO.insert throws', async () => {
      mockDAO.insert.mockRejectedValue(new Error('Connection refused'));

      try {
        await PrimaryKpiService.record(validRequest);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(KpiError);
        expect((e as KpiError).code).toBe('PERSISTENCE_ERROR');
        expect((e as KpiError).statusCode).toBe(500);
        expect((e as KpiError).retryable).toBe(true);
      }
    });

    it('should NOT set analyticsEmitted to true when DAO.insert throws', async () => {
      mockDAO.insert.mockRejectedValue(new Error('Write failed'));

      try {
        await PrimaryKpiService.record(validRequest);
        expect.fail('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(KpiError);
        // No result returned — analytics emitter never called
      }

      expect(mockDAO.updateStatus).not.toHaveBeenCalled();
    });

    it('should log error via kpiLogger when DAO.insert throws', async () => {
      const dbError = new Error('Connection refused');
      mockDAO.insert.mockRejectedValue(dbError);

      try {
        await PrimaryKpiService.record(validRequest);
        expect.fail('Should have thrown');
      } catch {
        // Expected
      }

      expect(mockLogger.error).toHaveBeenCalledWith(
        expect.stringContaining('persist'),
        dbError,
        expect.objectContaining({
          userId: validRequest.userId,
          actionType: validRequest.actionType,
        }),
      );
    });

    it('should log error via kpiLogger when business rule validation fails', async () => {
      const invalidRequest: RecordPrimaryKpiRequest = {
        userId: '',
        actionType: 'purchase',
      };

      try {
        await PrimaryKpiService.record(invalidRequest);
        expect.fail('Should have thrown');
      } catch {
        // Expected
      }

      expect(mockLogger.error).toHaveBeenCalled();
    });

    it('should NOT call kpiLogger.info when DAO.insert throws', async () => {
      mockDAO.insert.mockRejectedValue(new Error('DB unavailable'));

      try {
        await PrimaryKpiService.record(validRequest);
        expect.fail('Should have thrown');
      } catch {
        // Expected
      }

      expect(mockLogger.info).not.toHaveBeenCalled();
    });

    it('should NOT call kpiLogger.info when business rule validation fails', async () => {
      const invalidRequest: RecordPrimaryKpiRequest = {
        userId: '',
        actionType: 'purchase',
      };

      try {
        await PrimaryKpiService.record(invalidRequest);
        expect.fail('Should have thrown');
      } catch {
        // Expected
      }

      expect(mockLogger.info).not.toHaveBeenCalled();
    });
  });
});
