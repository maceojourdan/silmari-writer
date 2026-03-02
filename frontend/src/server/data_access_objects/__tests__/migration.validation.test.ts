import { describe, it, expect } from 'vitest';
import { readFileSync, existsSync } from 'fs';
import { resolve } from 'path';

const MIGRATION_PATH = resolve(__dirname, '../../../../../supabase/migrations/20260302000000_initial_schema.sql');

describe('SQL Migration Validation', () => {
  it('migration file exists', () => {
    expect(existsSync(MIGRATION_PATH)).toBe(true);
  });

  it('contains all 32 required tables', () => {
    const sql = readFileSync(MIGRATION_PATH, 'utf-8').toLowerCase();
    const requiredTables = [
      // Tier 1: no FK dependencies
      'users', 'resumes', 'jobs', 'questions',
      // Tier 2: depend on Tier 1
      'sessions', 'job_requirements', 'claimants',
      'answer_sessions', 'cases', 'stories', 'onboarding',
      // Tier 3: depend on Tier 2
      'analytics_events', 'primary_kpi_events', 'events',
      'session_metrics', 'session_slots',
      'story_records', 'behavioral_questions', 'drafts',
      'answers', 'content', 'orient_story_records',
      // Tier 4: depend on Tier 3
      'claims', 'sms_follow_ups',
      'truth_checks', 'verification_requests', 'drafting_workflows',
      // Tier 5: depend on Tier 4
      'delivery_attempts',
      'verification_attempts',
      'draft_metrics',
      'draft_versions',
      'story_metrics',
    ];
    for (const table of requiredTables) {
      expect(sql).toContain(`create table if not exists ${table}`);
    }
  });

  it('contains confirm_story RPC function', () => {
    const sql = readFileSync(MIGRATION_PATH, 'utf-8').toLowerCase();
    expect(sql).toContain('create or replace function confirm_story');
  });

  it('uses UUID defaults via gen_random_uuid()', () => {
    const sql = readFileSync(MIGRATION_PATH, 'utf-8');
    expect(sql).toContain('gen_random_uuid()');
  });

  it('creates tables in FK dependency order (no forward references)', () => {
    const sql = readFileSync(MIGRATION_PATH, 'utf-8').toLowerCase();
    // Tier 1 tables should appear before Tier 2+ tables
    const usersIdx = sql.indexOf('create table if not exists users');
    const sessionsIdx = sql.indexOf('create table if not exists sessions');
    const claimsIdx = sql.indexOf('create table if not exists claims');
    expect(usersIdx).toBeLessThan(sessionsIdx);
    expect(sessionsIdx).toBeLessThan(claimsIdx);
  });

  it('has CHECK constraints for status enums', () => {
    const sql = readFileSync(MIGRATION_PATH, 'utf-8').toLowerCase();
    expect(sql).toContain('check');
  });

  it('has indexes on FK columns', () => {
    const sql = readFileSync(MIGRATION_PATH, 'utf-8').toLowerCase();
    expect(sql).toContain('create index');
  });
});
