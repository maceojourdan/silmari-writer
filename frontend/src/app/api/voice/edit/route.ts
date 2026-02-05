import { NextRequest, NextResponse } from 'next/server';
import OpenAI from 'openai';

interface DocumentContextItem {
  messageId: string;
  content: string;
}

export async function POST(request: NextRequest) {
  const apiKey = process.env.OPENAI_API_KEY;
  if (!apiKey) {
    return NextResponse.json({ error: 'Not configured' }, { status: 500 });
  }

  const body = await request.json();
  const { instruction, messageContent, messageId, documentContext } = body;

  if (!instruction || !messageContent || !messageId) {
    return NextResponse.json(
      { error: 'Missing required fields: instruction, messageContent, messageId' },
      { status: 400 },
    );
  }

  const openai = new OpenAI({ apiKey });

  const systemPrompt = buildSystemPrompt(messageContent, messageId, documentContext);

  try {
    const completion = await openai.chat.completions.create({
      model: 'gpt-4o-mini',
      temperature: 0.3,
      messages: [
        { role: 'system', content: systemPrompt },
        { role: 'user', content: instruction },
      ],
      response_format: { type: 'json_object' },
    });

    let result: { edited_content?: string; edit_summary?: string };
    try {
      result = JSON.parse(completion.choices[0].message.content ?? '{}');
    } catch {
      return NextResponse.json({
        editedContent: messageContent,
        editSummary: 'Edit could not be applied (invalid response)',
        messageId,
      });
    }

    return NextResponse.json({
      editedContent: result.edited_content ?? messageContent,
      editSummary: result.edit_summary ?? '',
      messageId,
    });
  } catch (err) {
    const status = (err as { status?: number }).status;
    if (status === 429) {
      return NextResponse.json({ error: 'Rate limited' }, { status: 503 });
    }
    return NextResponse.json({ error: 'Edit failed' }, { status: 502 });
  }
}

function buildSystemPrompt(
  messageContent: string,
  messageId: string,
  documentContext?: DocumentContextItem[],
): string {
  let context = '';
  if (documentContext?.length) {
    context = `\n\nFULL DOCUMENT CONTEXT:\n${documentContext
      .map((d) => `[Message ${d.messageId}]:\n${d.content}`)
      .join('\n\n---\n\n')}`;
  }

  return `You are a precise text editing assistant. Apply the user's edit instruction to the target message.

TARGET MESSAGE (ID: ${messageId}):
${messageContent}
${context}

Respond with a JSON object containing:
- "edited_content": The complete edited text of the target message
- "edit_summary": A brief summary of what was changed

Important:
- Return the COMPLETE edited text, not just the changed parts
- Preserve all formatting (markdown, line breaks, etc.)
- Only change what the instruction asks for
- If the instruction is unclear, make your best interpretation`;
}
