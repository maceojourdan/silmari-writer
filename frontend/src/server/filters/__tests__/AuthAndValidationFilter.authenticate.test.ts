import { describe, expect, it } from 'vitest';
import { createHash } from 'crypto';
import { AuthAndValidationFilter } from '../AuthAndValidationFilter';
import { StoryError } from '@/server/error_definitions/StoryErrors';

function toBase64Url(value: string): string {
  return Buffer.from(value)
    .toString('base64')
    .replace(/\+/g, '-')
    .replace(/\//g, '_')
    .replace(/=+$/g, '');
}

function createJwt(sub: string): string {
  const header = toBase64Url(JSON.stringify({ alg: 'HS256', typ: 'JWT' }));
  const payload = toBase64Url(JSON.stringify({ sub }));
  const signature = 'signature';
  return `${header}.${payload}.${signature}`;
}

function expectedHashedUserId(value: string): string {
  return `user-${createHash('sha256').update(value).digest('hex').slice(0, 16)}`;
}

describe('AuthAndValidationFilter.authenticate', () => {
  it('derives unique deterministic userId values from JWT sub claims', () => {
    const tokenA = createJwt('user-A');
    const tokenB = createJwt('user-B');
    const tokenAWithDifferentSignature = `${tokenA.split('.').slice(0, 2).join('.')}.other-signature`;

    const authA = AuthAndValidationFilter.authenticate(`Bearer ${tokenA}`);
    const authB = AuthAndValidationFilter.authenticate(`Bearer ${tokenB}`);
    const authA2 = AuthAndValidationFilter.authenticate(`Bearer ${tokenAWithDifferentSignature}`);

    expect(authA.userId).toBe(expectedHashedUserId('user-A'));
    expect(authB.userId).toBe(expectedHashedUserId('user-B'));
    expect(authA.userId).not.toBe(authB.userId);
    expect(authA.userId).toBe(authA2.userId);
    expect(authA.authenticated).toBe(true);
  });

  it('falls back to deterministic token hashing for non-JWT tokens', () => {
    const tokenA = 'plain-token-a';
    const tokenB = 'plain-token-b';

    const authA = AuthAndValidationFilter.authenticate(`Bearer ${tokenA}`);
    const authB = AuthAndValidationFilter.authenticate(`Bearer ${tokenB}`);
    const authA2 = AuthAndValidationFilter.authenticate(`Bearer ${tokenA}`);

    expect(authA.userId).toBe(expectedHashedUserId(`token:${tokenA}`));
    expect(authB.userId).toBe(expectedHashedUserId(`token:${tokenB}`));
    expect(authA.userId).not.toBe(authB.userId);
    expect(authA.userId).toBe(authA2.userId);
  });

  it('throws UNAUTHORIZED for missing or empty auth headers', () => {
    expect(() => AuthAndValidationFilter.authenticate(undefined)).toThrow(StoryError);
    expect(() => AuthAndValidationFilter.authenticate('')).toThrow(StoryError);
    expect(() => AuthAndValidationFilter.authenticate('Bearer ')).toThrow(StoryError);
  });
});
