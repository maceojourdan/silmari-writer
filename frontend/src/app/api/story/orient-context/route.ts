/**
 * GET /api/story/orient-context
 *
 * Resource: api-m5g7 (endpoint)
 * Path: 313-confirm-aligned-story-selection
 *
 * Fetches the question, job requirements, and available stories
 * for display on the orient story selection screen.
 */

import { NextRequest, NextResponse } from 'next/server';
import { ConfirmStoryDAO } from '@/server/data_access_objects/ConfirmStoryDAO';
import { ConfirmStoryError, ConfirmStoryErrors } from '@/server/error_definitions/ConfirmStoryErrors';

export async function GET(request: NextRequest) {
  try {
    const { searchParams } = new URL(request.url);
    const questionId = searchParams.get('questionId');

    if (!questionId) {
      return NextResponse.json(
        { code: 'INVALID_REQUEST', message: 'questionId query parameter is required' },
        { status: 400 },
      );
    }

    // 1. Fetch question
    const question = await ConfirmStoryDAO.findQuestionById(questionId);
    if (!question) {
      throw ConfirmStoryErrors.DataNotFound(`Question not found: ${questionId}`);
    }

    // 2. Fetch job requirements
    const jobRequirements = await ConfirmStoryDAO.findJobRequirementsByQuestionId(questionId);
    if (jobRequirements.length === 0) {
      throw ConfirmStoryErrors.DataNotFound(`No job requirements found for question: ${questionId}`);
    }

    // 3. Fetch stories
    const stories = await ConfirmStoryDAO.findStoriesByQuestionId(questionId);
    if (stories.length === 0) {
      throw ConfirmStoryErrors.DataNotFound(`No stories found for question: ${questionId}`);
    }

    return NextResponse.json({
      question,
      jobRequirements,
      stories,
    });
  } catch (error) {
    if (error instanceof ConfirmStoryError) {
      return NextResponse.json(
        { code: error.code, message: error.message },
        { status: error.statusCode },
      );
    }

    console.error('[orient-context] Unexpected error:', error);
    return NextResponse.json(
      { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' },
      { status: 500 },
    );
  }
}
