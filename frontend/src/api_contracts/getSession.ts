import { SessionViewSchema, type SessionView } from '@/server/data_structures/SessionView';

export async function getSession(sessionId: string): Promise<SessionView> {
  const response = await fetch(`/api/sessions/${sessionId}`);

  if (!response.ok) {
    const errorBody = await response.json().catch(() => ({}));
    throw new Error(
      errorBody.message || `Failed to load session with status ${response.status}`,
    );
  }

  const data = await response.json();
  const parsed = SessionViewSchema.safeParse(data);

  if (!parsed.success) {
    throw new Error(
      `Invalid response from sessions endpoint: ${parsed.error.issues.map((issue) => issue.message).join(', ')}`,
    );
  }

  return parsed.data;
}

