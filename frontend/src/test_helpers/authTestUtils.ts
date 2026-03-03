import { AuthAndValidationFilter } from '@/server/filters/AuthAndValidationFilter';

export function deriveUserIdForToken(token: string): string {
  return AuthAndValidationFilter.authenticate(`Bearer ${token}`).userId;
}
