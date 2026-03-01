/**
 * Supabase client stub.
 *
 * In production, this will be initialized with the Supabase project URL
 * and anon key. Currently a stub for TDD - all DAOs are mockable.
 */

// Placeholder: will be replaced with real Supabase client initialization
// e.g., import { createClient } from '@supabase/supabase-js';
// export const supabase = createClient(process.env.NEXT_PUBLIC_SUPABASE_URL!, process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY!);

export const supabase = {
  from(_table: string) {
    throw new Error('Supabase client not yet initialized. Wire up environment variables.');
  },
} as any;
