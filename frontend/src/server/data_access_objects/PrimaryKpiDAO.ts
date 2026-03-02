/**
 * PrimaryKpiDAO - Handles database persistence for primary KPI event records.
 *
 * Resource: db-d3w8 (data_access_object)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * In production, each method performs Supabase queries. For TDD, methods are designed to be mockable.
 */

import type { PrimaryKpiRecord, PrimaryKpiInsert } from '@/server/data_structures/PrimaryKpiRecord';
import { supabase } from '@/lib/supabase';
import { KpiErrors, KpiError } from '@/server/error_definitions/KpiErrors';

export const PrimaryKpiDAO = {
  async insert(data: PrimaryKpiInsert): Promise<PrimaryKpiRecord> {
    try {
      const { data: row, error } = await supabase
        .from('primary_kpi_events')
        .insert({
          user_id: data.userId,
          action_type: data.actionType,
          metadata: data.metadata,
          status: data.status,
          timestamp: data.timestamp,
        })
        .select()
        .single();

      if (error) throw KpiErrors.PersistenceError(`Failed to insert KPI record: ${error.message}`);
      if (!row) throw KpiErrors.PersistenceError('No data returned');

      return {
        id: row.id,
        userId: row.user_id,
        actionType: row.action_type,
        metadata: row.metadata,
        status: row.status,
        timestamp: row.timestamp,
        createdAt: row.created_at,
      } as PrimaryKpiRecord;
    } catch (err) {
      if (err instanceof KpiError) throw err;
      throw KpiErrors.PersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },

  async findById(id: string): Promise<PrimaryKpiRecord | null> {
    try {
      const { data, error } = await supabase
        .from('primary_kpi_events')
        .select('*')
        .eq('id', id)
        .maybeSingle();

      if (error) throw KpiErrors.PersistenceError(`Failed to find KPI record: ${error.message}`);
      if (!data) return null;

      return {
        id: data.id,
        userId: data.user_id,
        actionType: data.action_type,
        metadata: data.metadata,
        status: data.status,
        timestamp: data.timestamp,
        createdAt: data.created_at,
      } as PrimaryKpiRecord;
    } catch (err) {
      if (err instanceof KpiError) throw err;
      throw KpiErrors.PersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },

  async updateStatus(id: string, status: PrimaryKpiRecord['status']): Promise<PrimaryKpiRecord> {
    try {
      const { data, error } = await supabase
        .from('primary_kpi_events')
        .update({ status })
        .eq('id', id)
        .select()
        .single();

      if (error) throw KpiErrors.PersistenceError(`Failed to update KPI status: ${error.message}`);
      if (!data) throw KpiErrors.PersistenceError('No data returned');

      return {
        id: data.id,
        userId: data.user_id,
        actionType: data.action_type,
        metadata: data.metadata,
        status: data.status,
        timestamp: data.timestamp,
        createdAt: data.created_at,
      } as PrimaryKpiRecord;
    } catch (err) {
      if (err instanceof KpiError) throw err;
      throw KpiErrors.PersistenceError(`Unexpected: ${(err as Error).message}`);
    }
  },
} as const;
