import type { PostgrestError } from '@supabase/supabase-js';

interface QueryResult<T> {
  data: T;
  error: PostgrestError | null;
}

function formatError(context: string, error: PostgrestError): Error {
  return new Error(`${context}: ${error.message}`);
}

export function assertNoError(context: string, error: PostgrestError | null): void {
  if (error) {
    throw formatError(context, error);
  }
}

export async function singleOrThrow<T>(
  context: string,
  promise: Promise<QueryResult<T | null>>,
): Promise<T> {
  const { data, error } = await promise;
  assertNoError(context, error);

  if (data === null) {
    throw new Error(`${context}: no row returned`);
  }

  return data;
}

export async function maybeSingleOrNull<T>(
  context: string,
  promise: Promise<QueryResult<T | null>>,
): Promise<T | null> {
  const { data, error } = await promise;

  if (error && error.code === 'PGRST116') {
    return null;
  }

  assertNoError(context, error);
  return data;
}

export async function listOrThrow<T>(
  context: string,
  promise: Promise<QueryResult<T[] | null>>,
): Promise<T[]> {
  const { data, error } = await promise;
  assertNoError(context, error);
  return data ?? [];
}

export function nowIso(): string {
  return new Date().toISOString();
}
