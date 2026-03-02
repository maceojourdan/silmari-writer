/**
 * SmsFollowUpDAO Wiring Tests
 */
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { SmsError } from '@/server/error_definitions/SmsErrors';

const { mockSingle, mockSelect, mockInsert, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockSelect = vi.fn();
  const mockInsert = vi.fn();
  const mockFrom = vi.fn();
  return { mockSingle, mockSelect, mockInsert, mockFrom };
});

vi.mock('@/lib/supabase', () => ({ supabase: { from: mockFrom } }));

import { SmsFollowUpDAO } from '../SmsFollowUpDAO';

const baseRow = {
  id: 'sms-1', answer_id: 'ans-1', phone_number: '+1234567890',
  message: 'Follow up', status: 'sent', message_id: 'ext-1',
  created_at: '2026-01-01',
};

describe('SmsFollowUpDAO — Supabase Wiring', () => {
  beforeEach(() => {
    vi.clearAllMocks();
    mockSelect.mockReturnValue({ single: mockSingle });
    mockInsert.mockReturnValue({ select: mockSelect });
    mockFrom.mockReturnValue({ insert: mockInsert });
  });

  // --- insert ---
  describe('insert', () => {
    describe('Reachability', () => {
      it('returns SmsFollowUpRecord with generated ID', async () => {
        mockSingle.mockResolvedValue({ data: baseRow, error: null });
        const result = await SmsFollowUpDAO.insert({
          answerId: 'ans-1', phoneNumber: '+1234567890',
          message: 'Follow up', status: 'sent', messageId: 'ext-1',
          createdAt: '2026-01-01',
        });
        expect(result.id).toBe('sms-1');
        expect(mockFrom).toHaveBeenCalledWith('sms_follow_ups');
      });
    });
    describe('ErrorConsistency', () => {
      it('throws SmsError on failure', async () => {
        mockSingle.mockResolvedValue({ data: null, error: { message: 'fail' } });
        await expect(SmsFollowUpDAO.insert({
          answerId: 'ans-1', phoneNumber: '+1234567890',
          message: 'Follow up', status: 'sent', createdAt: '2026-01-01',
        })).rejects.toThrow(SmsError);
      });
    });
  });
});
