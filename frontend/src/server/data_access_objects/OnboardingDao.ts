/**
 * OnboardingDao - Handles database persistence for onboarding entities
 * and analytics events.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 338-record-leading-kpi-analytics-event-on-successful-user-action
 *
 * In production, each method performs Supabase queries. For TDD, methods are designed to be mockable.
 */

import type { Onboarding } from '@/server/data_structures/Onboarding';
import type {
  AnalyticsEvent,
  AnalyticsEventInsert,
} from '@/server/data_structures/AnalyticsEvent';

export const OnboardingDao = {
  /**
   * Find an onboarding record for a user and step.
   * Returns null if not found.
   */
  async findByUserAndStep(
    userId: string,
    step: number,
  ): Promise<Onboarding | null> {
    // Supabase: supabase.from('onboarding').select('*').eq('userId', userId).eq('step', step).single()
    throw new Error('OnboardingDao.findByUserAndStep not yet wired to Supabase');
  },

  /**
   * Update an onboarding record's status to completed.
   * Returns the updated onboarding entity.
   * Throws on database failure.
   */
  async updateOnboardingStep(
    userId: string,
    step: number,
    fields: Partial<Pick<Onboarding, 'status' | 'completedAt' | 'updatedAt'>>,
  ): Promise<Onboarding> {
    // Supabase: supabase.from('onboarding').update({ ...fields }).eq('userId', userId).eq('step', step).select().single()
    throw new Error(
      'OnboardingDao.updateOnboardingStep not yet wired to Supabase',
    );
  },

  /**
   * Create a new onboarding record.
   * Returns the created onboarding entity.
   */
  async createOnboarding(
    data: Pick<Onboarding, 'userId' | 'step'>,
  ): Promise<Onboarding> {
    // Supabase: supabase.from('onboarding').insert([{ ...data, status: 'NOT_STARTED' }]).select().single()
    throw new Error('OnboardingDao.createOnboarding not yet wired to Supabase');
  },

  /**
   * Insert an analytics event record.
   * Returns the created analytics event.
   * Throws on database failure.
   */
  async insertAnalyticsEvent(
    data: AnalyticsEventInsert,
  ): Promise<AnalyticsEvent> {
    // Supabase: supabase.from('analytics_events').insert([{ ...data, id: uuid(), createdAt: now() }]).select().single()
    throw new Error(
      'OnboardingDao.insertAnalyticsEvent not yet wired to Supabase',
    );
  },

  /**
   * Find an analytics event by userId and kpiId (for idempotency checks).
   * Returns null if not found.
   */
  async findAnalyticsEvent(
    userId: string,
    kpiId: string,
    metadata: Record<string, unknown>,
  ): Promise<AnalyticsEvent | null> {
    // Supabase: supabase.from('analytics_events').select('*').eq('userId', userId).eq('kpiId', kpiId).single()
    throw new Error(
      'OnboardingDao.findAnalyticsEvent not yet wired to Supabase',
    );
  },
} as const;
