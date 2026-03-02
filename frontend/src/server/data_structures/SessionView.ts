import { z } from 'zod';

export const SessionViewSourceSchema = z.enum(['answer_session', 'session']);

export const SessionViewSchema = z.object({
  id: z.string().uuid(),
  state: z.string().min(1),
  source: SessionViewSourceSchema,
  createdAt: z.string(),
  updatedAt: z.string(),
});

export type SessionView = z.infer<typeof SessionViewSchema>;

