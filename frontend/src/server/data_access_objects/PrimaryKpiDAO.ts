/**
 * PrimaryKpiDAO - Handles database persistence for primary KPI event records.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * In production, each method performs Supabase queries. For TDD, methods are designed to be mockable.
 */

import type { PrimaryKpiRecord, PrimaryKpiInsert } from '@/server/data_structures/PrimaryKpiRecord';

export const PrimaryKpiDAO = {
  /**
   * Insert a new primary KPI record.
   * Returns the persisted record with generated id and createdAt.
   */
  async insert(data: PrimaryKpiInsert): Promise<PrimaryKpiRecord> {
    // Supabase: supabase.from('primary_kpi_events').insert(data).select().single()
    throw new Error('PrimaryKpiDAO.insert not yet wired to Supabase');
  },

  /**
   * Find a primary KPI record by its ID.
   * Returns null if not found.
   */
  async findById(id: string): Promise<PrimaryKpiRecord | null> {
    // Supabase: supabase.from('primary_kpi_events').select('*').eq('id', id).single()
    throw new Error('PrimaryKpiDAO.findById not yet wired to Supabase');
  },

  /**
   * Update the status of a primary KPI record.
   * Returns the updated record.
   */
  async updateStatus(id: string, status: PrimaryKpiRecord['status']): Promise<PrimaryKpiRecord> {
    // Supabase: supabase.from('primary_kpi_events').update({ status }).eq('id', id).select().single()
    throw new Error('PrimaryKpiDAO.updateStatus not yet wired to Supabase');
  },
} as const;
