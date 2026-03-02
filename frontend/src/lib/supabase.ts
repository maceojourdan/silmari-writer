import { createClient } from '@supabase/supabase-js';

const supabaseUrl = process.env.NEXT_PUBLIC_SUPABASE_URL;

// Preferred: publishable key (new API key scheme).
// Backward compatibility: fallback to legacy anon key naming.
const supabaseKey =
  process.env.NEXT_PUBLIC_SUPABASE_PUBLISHABLE_KEY ||
  process.env.NEXT_PUBLIC_SUPABASE_PUBLISHABLE_DEFAULT_KEY ||
  process.env.NEXT_PUBLIC_SUPABASE_ANON_KEY;

const missingConfigError =
  'Supabase client not initialized. Set NEXT_PUBLIC_SUPABASE_URL and a key: NEXT_PUBLIC_SUPABASE_PUBLISHABLE_KEY (preferred), NEXT_PUBLIC_SUPABASE_PUBLISHABLE_DEFAULT_KEY, or NEXT_PUBLIC_SUPABASE_ANON_KEY.';

export const supabase =
  supabaseUrl && supabaseKey
    ? createClient(supabaseUrl, supabaseKey, {
        auth: {
          persistSession: false,
          autoRefreshToken: false,
        },
      })
    : ({
        from(_table: string) {
          throw new Error(missingConfigError);
        },
      } as any);
