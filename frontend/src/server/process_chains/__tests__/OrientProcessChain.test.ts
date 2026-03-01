/**
 * Tests for OrientProcessChain.startOrientProcess
 *
 * Resource: mq-r4z8 (backend_process_chain)
 * Path: 295-orient-state-creates-single-story-record
 *
 * TLA+ properties tested:
 * - Reachability: Call startOrientProcess with experiences → returned context contains experiences
 * - TypeInvariant: Returned object matches OrientExecutionContext type
 * - ErrorConsistency: Unregistered chain → BackendError with SYSTEM_PROCESS_CHAIN_NOT_FOUND
 */

import { describe, it, expect } from 'vitest';
import { z } from 'zod';
import { OrientProcessChain } from '../OrientProcessChain';
import { OrientError } from '../../error_definitions/OrientErrors';
import {
  OrientExecutionContextSchema,
  type Experience,
} from '../../data_structures/OrientStoryRecord';

const validExperiences: Experience[] = [
  { id: 'exp-1', title: 'Led migration to microservices', summary: 'Broke monolith into 12 services' },
  { id: 'exp-2', title: 'Built real-time analytics', summary: 'Streaming pipeline processing 1M events/s' },
];

describe('OrientProcessChain.startOrientProcess', () => {
  describe('Reachability: valid experiences → context with experiences', () => {
    it('should return execution context containing the provided experiences', () => {
      const context = OrientProcessChain.startOrientProcess({
        experiences: validExperiences,
      });

      expect(context.experiences).toEqual(validExperiences);
      expect(context.experiences).toHaveLength(2);
    });
  });

  describe('TypeInvariant: returned object matches OrientExecutionContext', () => {
    it('should return an object that satisfies OrientExecutionContextSchema', () => {
      const context = OrientProcessChain.startOrientProcess({
        experiences: validExperiences,
      });

      const parsed = OrientExecutionContextSchema.safeParse(context);
      expect(parsed.success).toBe(true);
    });

    it('should have experiences as Experience[]', () => {
      const context = OrientProcessChain.startOrientProcess({
        experiences: validExperiences,
      });

      expect(Array.isArray(context.experiences)).toBe(true);
      for (const exp of context.experiences) {
        expect(exp).toHaveProperty('id');
        expect(exp).toHaveProperty('title');
        expect(exp).toHaveProperty('summary');
        expect(typeof exp.id).toBe('string');
        expect(typeof exp.title).toBe('string');
        expect(typeof exp.summary).toBe('string');
      }
    });
  });

  describe('ErrorConsistency: unregistered chain → SYSTEM_PROCESS_CHAIN_NOT_FOUND', () => {
    it('should throw OrientError when chain is not registered', () => {
      expect(() =>
        OrientProcessChain.startOrientProcess(
          { experiences: validExperiences },
          { registryOverride: new Map() }, // empty registry = chain not registered
        ),
      ).toThrow(OrientError);
    });

    it('should throw with code SYSTEM_PROCESS_CHAIN_NOT_FOUND', () => {
      try {
        OrientProcessChain.startOrientProcess(
          { experiences: validExperiences },
          { registryOverride: new Map() },
        );
        expect.unreachable('Should have thrown');
      } catch (e) {
        expect(e).toBeInstanceOf(OrientError);
        expect((e as OrientError).code).toBe('SYSTEM_PROCESS_CHAIN_NOT_FOUND');
      }
    });
  });
});
