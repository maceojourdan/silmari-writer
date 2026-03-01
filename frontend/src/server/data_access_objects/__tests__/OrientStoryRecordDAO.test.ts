/**
 * Tests for OrientStoryRecordDAO
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 295-orient-state-creates-single-story-record
 *
 * TLA+ properties tested:
 * - Reachability: Mock Supabase → insertStoryRecord(validRecord) → one insert, returned record has id
 * - TypeInvariant: Returned object matches OrientStoryRecord with id: string
 * - ErrorConsistency: DB error → STORY_RECORD_PERSISTENCE_FAILED, no partial state
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { OrientError } from '../../error_definitions/OrientErrors';
import {
  OrientStoryRecordSchema,
  type OrientStoryRecord,
} from '../../data_structures/OrientStoryRecord';

// Use vi.hoisted so mock fns are available before the hoisted vi.mock call
const { mockSingle, mockSelect, mockInsert, mockFrom } = vi.hoisted(() => {
  const mockSingle = vi.fn();
  const mockSelect = vi.fn(() => ({ single: mockSingle }));
  const mockInsert = vi.fn(() => ({ select: mockSelect }));
  const mockFrom = vi.fn(() => ({ insert: mockInsert }));
  return { mockSingle, mockSelect, mockInsert, mockFrom };
});

vi.mock('@/lib/supabase', () => ({
  supabase: {
    from: mockFrom,
  },
}));

import { OrientStoryRecordDAO } from '../OrientStoryRecordDAO';

const validRecord: OrientStoryRecord = {
  story_title: 'Led migration to microservices',
  initial_context: {
    experienceId: 'exp-1',
    summary: 'Broke monolith into 12 services',
  },
};

const persistedRecord: OrientStoryRecord = {
  ...validRecord,
  id: '550e8400-e29b-41d4-a716-446655440099',
  createdAt: '2026-03-01T00:00:00.000Z',
};

describe('OrientStoryRecordDAO', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe('Reachability: valid record → one insert, returned record has id', () => {
    it('should insert one record and return it with an id', async () => {
      mockSingle.mockResolvedValue({ data: persistedRecord, error: null });

      const result = await OrientStoryRecordDAO.insertStoryRecord(validRecord);

      expect(mockFrom).toHaveBeenCalledWith('orient_story_records');
      expect(mockInsert).toHaveBeenCalledTimes(1);
      expect(result.id).toBe('550e8400-e29b-41d4-a716-446655440099');
      expect(result.story_title).toBe('Led migration to microservices');
    });
  });

  describe('TypeInvariant: returned object matches OrientStoryRecord with id', () => {
    it('should return record that satisfies OrientStoryRecordSchema', async () => {
      mockSingle.mockResolvedValue({ data: persistedRecord, error: null });

      const result = await OrientStoryRecordDAO.insertStoryRecord(validRecord);

      const parsed = OrientStoryRecordSchema.safeParse(result);
      expect(parsed.success).toBe(true);
    });

    it('should have id as a string', async () => {
      mockSingle.mockResolvedValue({ data: persistedRecord, error: null });

      const result = await OrientStoryRecordDAO.insertStoryRecord(validRecord);

      expect(typeof result.id).toBe('string');
      expect(result.id!.length).toBeGreaterThan(0);
    });
  });

  describe('ErrorConsistency: DB error → STORY_RECORD_PERSISTENCE_FAILED', () => {
    it('should throw OrientError on database error', async () => {
      mockSingle.mockResolvedValue({
        data: null,
        error: { message: 'Connection refused', code: 'PGRST000' },
      });

      await expect(
        OrientStoryRecordDAO.insertStoryRecord(validRecord),
      ).rejects.toThrow(OrientError);
    });

    it('should throw with code STORY_RECORD_PERSISTENCE_FAILED', async () => {
      mockSingle.mockResolvedValue({
        data: null,
        error: { message: 'Unique constraint violation', code: '23505' },
      });

      try {
        await OrientStoryRecordDAO.insertStoryRecord(validRecord);
        expect.unreachable('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(OrientError);
        expect((e as OrientError).code).toBe('STORY_RECORD_PERSISTENCE_FAILED');
        expect((e as OrientError).retryable).toBe(true);
      }
    });

    it('should throw when data is null (no partial state)', async () => {
      mockSingle.mockResolvedValue({ data: null, error: null });

      await expect(
        OrientStoryRecordDAO.insertStoryRecord(validRecord),
      ).rejects.toThrow(OrientError);
    });
  });
});
