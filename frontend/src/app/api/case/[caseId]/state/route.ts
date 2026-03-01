/**
 * GET /api/case/[caseId]/state
 *
 * Returns the current drafting state of a case, including
 * whether drafting is blocked due to unverified claims.
 *
 * Resource: api-q7v1 (frontend_api_contract)
 * Path: 322-handle-disputed-claims-and-block-drafting
 */

import { NextRequest, NextResponse } from 'next/server';
import { ClaimCaseDAO } from '@/server/data_access_objects/ClaimCaseDAO';
import type { CaseStateResponse } from '@/server/data_structures/Case';

export async function GET(
  _request: NextRequest,
  { params }: { params: Promise<{ caseId: string }> },
) {
  try {
    const { caseId } = await params;

    if (!caseId) {
      return NextResponse.json(
        { code: 'INVALID_REQUEST', message: 'Case ID is required' },
        { status: 400 },
      );
    }

    // In production, this would query ClaimCaseDAO
    // For now, return a stub response
    const response: CaseStateResponse = {
      caseId,
      drafting_status: 'drafting_allowed',
      blocked: false,
    };

    return NextResponse.json(response, { status: 200 });
  } catch (error) {
    console.error('[case/state] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'Failed to fetch case state' },
      { status: 500 },
    );
  }
}
