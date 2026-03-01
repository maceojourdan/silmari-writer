/**
 * VerificationRequestDAO - Encapsulates database operations for
 * verification request entities.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 321-verify-key-claims-via-voice-or-sms
 *
 * In production, each method performs Supabase queries.
 * For TDD, methods are designed to be mockable.
 */

import type {
  VerificationRequest,
  VerificationRequestStatus,
  DeliveryAttempt,
} from '@/server/data_structures/VerificationRequest';

export const VerificationRequestDAO = {
  /**
   * Create a new verification request record.
   */
  async create(data: {
    sessionId: string;
    claimIds: string[];
    contactPhone: string;
    contactMethod: 'sms' | 'voice';
    token: string;
  }): Promise<VerificationRequest> {
    // Supabase: supabase.from('verification_requests')
    //   .insert({ ...data, status: 'pending', attemptCount: 0 })
    //   .select()
    //   .single()
    throw new Error('VerificationRequestDAO.create not yet wired to Supabase');
  },

  /**
   * Find a verification request by token.
   */
  async findByToken(token: string): Promise<VerificationRequest | null> {
    // Supabase: supabase.from('verification_requests')
    //   .select('*')
    //   .eq('token', token)
    //   .eq('status', 'pending')
    //   .single()
    throw new Error('VerificationRequestDAO.findByToken not yet wired to Supabase');
  },

  /**
   * Find the latest verification request for a session.
   */
  async findBySessionId(sessionId: string): Promise<VerificationRequest | null> {
    // Supabase: supabase.from('verification_requests')
    //   .select('*')
    //   .eq('sessionId', sessionId)
    //   .order('createdAt', { ascending: false })
    //   .limit(1)
    //   .single()
    throw new Error('VerificationRequestDAO.findBySessionId not yet wired to Supabase');
  },

  /**
   * Update verification request status and attempt count.
   */
  async updateStatus(
    requestId: string,
    status: VerificationRequestStatus,
    attemptCount?: number,
  ): Promise<VerificationRequest> {
    // Supabase: supabase.from('verification_requests')
    //   .update({ status, attemptCount, updatedAt: new Date().toISOString() })
    //   .eq('id', requestId)
    //   .select()
    //   .single()
    throw new Error('VerificationRequestDAO.updateStatus not yet wired to Supabase');
  },

  /**
   * Log a delivery attempt for a verification request.
   */
  async logDeliveryAttempt(data: {
    requestId: string;
    attemptNumber: number;
    status: 'success' | 'failed';
    externalId?: string;
    errorMessage?: string;
  }): Promise<DeliveryAttempt> {
    // Supabase: supabase.from('delivery_attempts')
    //   .insert({ ...data })
    //   .select()
    //   .single()
    throw new Error('VerificationRequestDAO.logDeliveryAttempt not yet wired to Supabase');
  },

  // -------------------------------------------------------------------------
  // Path 324: verification-timeout-keeps-claims-unverified-and-drafting-on-hold
  // -------------------------------------------------------------------------

  /**
   * Find all pending verification requests that have no response.
   * Filters for status='pending' AND respondedAt IS NULL.
   */
  async findPendingUnresponded(): Promise<VerificationRequest[]> {
    // Supabase: supabase.from('verification_requests')
    //   .select('*')
    //   .eq('status', 'pending')
    //   .is('respondedAt', null)
    throw new Error('VerificationRequestDAO.findPendingUnresponded not yet wired to Supabase');
  },

  /**
   * Atomically update a verification request to a new status
   * only if respondedAt is still NULL (optimistic concurrency check).
   *
   * @returns Number of affected rows (0 if concurrently responded).
   */
  async updateStatusIfUnresponded(
    requestId: string,
    newStatus: VerificationRequestStatus,
  ): Promise<number> {
    // Supabase: supabase.from('verification_requests')
    //   .update({ status: newStatus, updatedAt: new Date().toISOString() })
    //   .eq('id', requestId)
    //   .is('respondedAt', null)
    //   → count affected rows
    throw new Error('VerificationRequestDAO.updateStatusIfUnresponded not yet wired to Supabase');
  },
} as const;
