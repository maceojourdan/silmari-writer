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

function escapeHtml(value: string): string {
  return value
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;')
    .replaceAll("'", '&#39;');
}

function asHtmlPage(
  body: {
    questionText: string;
    requirements: string[];
    stories: Array<{ title: string; summary: string }>;
  },
): string {
  const requirementItems = body.requirements
    .map((description) => `<li class="pill">${escapeHtml(description)}</li>`)
    .join('');
  const storyItems = body.stories
    .map((story) => (
      `<article class="story">
        <h3>${escapeHtml(story.title)}</h3>
        <p>${escapeHtml(story.summary)}</p>
      </article>`
    ))
    .join('');

  return `<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width,initial-scale=1" />
    <title>Orient Context</title>
    <style>
      :root {
        color-scheme: light dark;
      }
      body {
        margin: 0;
        background: linear-gradient(160deg, #f4f8ff 0%, #f7fafc 55%, #f3f4f6 100%);
        color: #111827;
        font: 16px/1.5 "Instrument Sans", "Segoe UI", sans-serif;
      }
      main {
        max-width: 900px;
        margin: 24px auto;
        padding: 0 16px 24px;
      }
      .card {
        border: 1px solid #dbe4f0;
        border-radius: 14px;
        background: #ffffff;
        padding: 16px;
        margin-bottom: 14px;
        box-shadow: 0 4px 16px rgb(15 23 42 / 0.06);
      }
      h1, h2, h3 {
        margin: 0 0 10px;
        line-height: 1.25;
      }
      h1 {
        font-size: 1.35rem;
      }
      h2 {
        font-size: 1rem;
        color: #1e3a8a;
      }
      h3 {
        font-size: 1rem;
      }
      p {
        margin: 0;
        color: #334155;
      }
      ul {
        list-style: none;
        margin: 0;
        padding: 0;
        display: grid;
        gap: 8px;
      }
      .pill {
        border: 1px solid #dbe4f0;
        border-radius: 10px;
        padding: 10px 12px;
        background: #f8fafc;
      }
      .stories {
        display: grid;
        gap: 10px;
      }
      .story {
        border: 1px solid #dbe4f0;
        border-radius: 10px;
        padding: 12px;
        background: #f8fafc;
      }
      @media (max-width: 640px) {
        main {
          margin-top: 12px;
          padding: 0 12px 16px;
        }
      }
    </style>
  </head>
  <body>
    <main>
      <section class="card">
        <h2>Behavioral Question</h2>
        <h1>${escapeHtml(body.questionText)}</h1>
      </section>
      <section class="card">
        <h2>Job Requirements</h2>
        <ul>${requirementItems}</ul>
      </section>
      <section class="card">
        <h2>Stories</h2>
        <div class="stories">${storyItems}</div>
      </section>
    </main>
  </body>
</html>`;
}

function asHtmlErrorPage(statusCode: number, code: string, message: string): string {
  return `<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width,initial-scale=1" />
    <title>${escapeHtml(code)}</title>
    <style>
      body { margin: 0; background: #fff7f7; color: #7f1d1d; font: 16px/1.5 "Instrument Sans", "Segoe UI", sans-serif; }
      main { max-width: 760px; margin: 24px auto; padding: 0 16px; }
      .card { border: 1px solid #fecaca; border-radius: 12px; background: #fef2f2; padding: 16px; }
      h1 { margin: 0 0 8px; font-size: 1.15rem; }
      p { margin: 0; }
      small { display: block; margin-top: 10px; opacity: 0.85; }
    </style>
  </head>
  <body>
    <main>
      <section class="card">
        <h1>${escapeHtml(code)}</h1>
        <p>${escapeHtml(message)}</p>
        <small>Status ${statusCode}</small>
      </section>
    </main>
  </body>
</html>`;
}

export async function GET(request: NextRequest) {
  try {
    const { searchParams } = new URL(request.url);
    const questionId = searchParams.get('questionId');
    const acceptsHtml = request.headers.get('accept')?.includes('text/html') ?? false;
    const view = searchParams.get('view');
    const shouldRenderHtml = acceptsHtml || view === 'html';

    if (!questionId) {
      const payload = { code: 'INVALID_REQUEST', message: 'questionId query parameter is required' };
      if (shouldRenderHtml) {
        return new NextResponse(asHtmlErrorPage(400, payload.code, payload.message), {
          status: 400,
          headers: { 'content-type': 'text/html; charset=utf-8' },
        });
      }
      return NextResponse.json(payload, { status: 400 });
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

    if (shouldRenderHtml) {
      return new NextResponse(
        asHtmlPage({
          questionText: question.text,
          requirements: jobRequirements.map((req) => req.description),
          stories: stories.map((story) => ({ title: story.title, summary: story.summary })),
        }),
        {
          status: 200,
          headers: { 'content-type': 'text/html; charset=utf-8' },
        },
      );
    }

    return NextResponse.json({ question, jobRequirements, stories });
  } catch (error) {
    if (error instanceof ConfirmStoryError) {
      const payload = { code: error.code, message: error.message };
      const acceptsHtml = request.headers.get('accept')?.includes('text/html') ?? false;
      const view = new URL(request.url).searchParams.get('view');
      const shouldRenderHtml = acceptsHtml || view === 'html';
      if (shouldRenderHtml) {
        return new NextResponse(asHtmlErrorPage(error.statusCode, payload.code, payload.message), {
          status: error.statusCode,
          headers: { 'content-type': 'text/html; charset=utf-8' },
        });
      }
      return NextResponse.json(payload, { status: error.statusCode });
    }

    console.error('[orient-context] Unexpected error:', error);
    const payload = { code: 'INTERNAL_ERROR', message: 'An unexpected error occurred' };
    const acceptsHtml = request.headers.get('accept')?.includes('text/html') ?? false;
    const view = new URL(request.url).searchParams.get('view');
    const shouldRenderHtml = acceptsHtml || view === 'html';
    if (shouldRenderHtml) {
      return new NextResponse(asHtmlErrorPage(500, payload.code, payload.message), {
        status: 500,
        headers: { 'content-type': 'text/html; charset=utf-8' },
      });
    }
    return NextResponse.json(payload, { status: 500 });
  }
}
