/**
 * generateDraft - Typed API contract for the draft generation endpoint.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Paths:
 *   - 325-generate-draft-from-confirmed-claims
 *   - 326-generate-draft-with-only-confirmed-claims
 *   - 327-prevent-draft-generation-without-confirmed-claims
 *   - 328-exclude-incomplete-claim-during-draft-generation
 */

import { z } from 'zod';
import { frontendLogger } from '@/logging/index';
import { SharedErrors } from '@/server/error_definitions/SharedErrors';
import { GenerateDraftResponseSchema } from '@/server/data_structures/StoryStructures';
import {
  GenerateCaseDraftResponseSchema,
  GenerateStoryDraftResponseSchema,
  ExcludeIncompleteDraftResponseSchema,
  ErrorResponseSchema,
} from '@/server/data_structures/Claim';
import type {
  GenerateCaseDraftResponse,
  GenerateStoryDraftResponse,
  ExcludeIncompleteDraftResponse,
  ErrorResponse,
} from '@/server/data_structures/Claim';

// ---------------------------------------------------------------------------
// Request Schema
// ---------------------------------------------------------------------------

export const GenerateDraftContractRequestSchema = z.object({
  claimSetId: z.string().uuid(),
});

export type GenerateDraftContractRequest = z.infer<typeof GenerateDraftContractRequestSchema>;

// ---------------------------------------------------------------------------
// Response Schema (re-exported from data structures)
// ---------------------------------------------------------------------------

export { GenerateDraftResponseSchema };
export type { GenerateDraftResponse } from '@/server/data_structures/StoryStructures';

// ---------------------------------------------------------------------------
// API Function
// ---------------------------------------------------------------------------

/**
 * Typed function that sends the generate-draft request.
 * Validates input via Zod schema before sending.
 * Validates response via Zod schema on receipt.
 * Logs errors via frontendLogger on failure.
 */
export async function generateDraft(
  request: { claimSetId: string },
): Promise<z.infer<typeof GenerateDraftResponseSchema>> {
  try {
    // Validate request before sending
    const parseResult = GenerateDraftContractRequestSchema.safeParse(request);
    if (!parseResult.success) {
      throw SharedErrors.MalformedRequest(
        `MALFORMED_REQUEST: ${parseResult.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    const response = await fetch('/api/generate-draft', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(parseResult.data),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      throw new Error(
        errorBody.message || `Generate draft request failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = GenerateDraftResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from generate-draft: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Generate draft request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'generateDraft', module: 'api_contracts' },
    );
    throw error;
  }
}

// ---------------------------------------------------------------------------
// Path 326: generate-draft-with-only-confirmed-claims
// ---------------------------------------------------------------------------

/**
 * Request schema for the case-based draft generation contract.
 */
export const GenerateCaseDraftContractRequestSchema = z.object({
  caseId: z.string().min(1),
});

export type GenerateCaseDraftContractRequest = z.infer<typeof GenerateCaseDraftContractRequestSchema>;

export { GenerateCaseDraftResponseSchema };
export type { GenerateCaseDraftResponse };

/**
 * Typed function that sends the case-based draft generation request.
 * Validates input and response via Zod schemas.
 * Logs errors via frontendLogger on failure.
 */
export async function generateCaseDraft(
  request: { caseId: string },
): Promise<GenerateCaseDraftResponse> {
  try {
    // Validate request before sending
    const parseResult = GenerateCaseDraftContractRequestSchema.safeParse(request);
    if (!parseResult.success) {
      throw SharedErrors.MalformedRequest(
        `MALFORMED_REQUEST: ${parseResult.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    const response = await fetch('/api/draft/generate', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(parseResult.data),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      throw new Error(
        errorBody.message || `Generate case draft request failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = GenerateCaseDraftResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from draft/generate: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Generate case draft request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'generateCaseDraft', module: 'api_contracts' },
    );
    throw error;
  }
}

// ---------------------------------------------------------------------------
// Path 327: prevent-draft-generation-without-confirmed-claims
// ---------------------------------------------------------------------------

/**
 * Request schema for the story-record-based draft generation contract.
 */
export const GenerateStoryDraftContractRequestSchema = z.object({
  storyRecordId: z.string().min(1),
});

export type GenerateStoryDraftContractRequest = z.infer<typeof GenerateStoryDraftContractRequestSchema>;

export { GenerateStoryDraftResponseSchema, ErrorResponseSchema };
export type { GenerateStoryDraftResponse, ErrorResponse };

/**
 * Typed function that sends the story-record-based draft generation request.
 * Validates input and response via Zod schemas.
 * Parses error responses into structured ErrorResponse objects.
 * Logs errors via frontendLogger on failure.
 */
export async function generateStoryDraft(
  request: { storyRecordId: string },
): Promise<GenerateStoryDraftResponse> {
  try {
    // Validate request before sending
    const parseResult = GenerateStoryDraftContractRequestSchema.safeParse(request);
    if (!parseResult.success) {
      throw SharedErrors.MalformedRequest(
        `MALFORMED_REQUEST: ${parseResult.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    const response = await fetch('/api/draft/generate', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(parseResult.data),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      // Parse as ErrorResponse if possible for structured error handling
      const errorParsed = ErrorResponseSchema.safeParse(errorBody);
      if (errorParsed.success) {
        const err = new Error(errorParsed.data.message);
        (err as any).code = errorParsed.data.code;
        throw err;
      }
      throw new Error(
        errorBody.message || `Generate story draft request failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = GenerateStoryDraftResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from draft/generate: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Generate story draft request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'generateStoryDraft', module: 'api_contracts' },
    );
    throw error;
  }
}

// ---------------------------------------------------------------------------
// Path 328: exclude-incomplete-claim-during-draft-generation
// ---------------------------------------------------------------------------

/**
 * Request schema for the exclude-incomplete draft generation contract.
 */
export const ExcludeIncompleteDraftContractRequestSchema = z.object({
  sessionId: z.string().min(1),
});

export type ExcludeIncompleteDraftContractRequest = z.infer<typeof ExcludeIncompleteDraftContractRequestSchema>;

export { ExcludeIncompleteDraftResponseSchema };
export type { ExcludeIncompleteDraftResponse };

/**
 * Typed function that sends the exclude-incomplete draft generation request.
 * Validates input and response via Zod schemas.
 * Parses error responses into structured ErrorResponse objects.
 * Logs errors via frontendLogger on failure.
 *
 * The response includes both the draft content (built from structurally
 * complete claims only) and an omission report listing claims that were
 * excluded due to missing required structural metadata.
 */
export async function generateDraftExcludingIncomplete(
  request: { sessionId: string },
): Promise<ExcludeIncompleteDraftResponse> {
  try {
    // Validate request before sending
    const parseResult = ExcludeIncompleteDraftContractRequestSchema.safeParse(request);
    if (!parseResult.success) {
      throw SharedErrors.MalformedRequest(
        `MALFORMED_REQUEST: ${parseResult.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    const response = await fetch('/api/draft/generate', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(parseResult.data),
    });

    if (!response.ok) {
      const errorBody = await response.json().catch(() => ({}));
      // Parse as ErrorResponse if possible for structured error handling
      const errorParsed = ErrorResponseSchema.safeParse(errorBody);
      if (errorParsed.success) {
        const err = new Error(errorParsed.data.message);
        (err as any).code = errorParsed.data.code;
        throw err;
      }
      throw new Error(
        errorBody.message || `Generate draft (exclude incomplete) request failed with status ${response.status}`,
      );
    }

    const data = await response.json();
    const parsed = ExcludeIncompleteDraftResponseSchema.safeParse(data);

    if (!parsed.success) {
      throw new Error(
        `Invalid response from draft/generate: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  } catch (error) {
    frontendLogger.error(
      'Generate draft (exclude incomplete) request failed',
      error instanceof Error ? error : new Error(String(error)),
      { action: 'generateDraftExcludingIncomplete', module: 'api_contracts' },
    );
    throw error;
  }
}
