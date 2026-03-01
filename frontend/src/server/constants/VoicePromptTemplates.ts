/**
 * VoicePromptTemplates - Constant prompt templates for voice follow-up
 * questions when required slots are missing.
 *
 * Resource: cfg-k3x7 (constant)
 * Path: 317-prompt-for-missing-slots-after-partial-voice-answer
 */

// ---------------------------------------------------------------------------
// Slot-specific follow-up prompt templates
// ---------------------------------------------------------------------------

export const SLOT_PROMPT_TEMPLATES: Record<string, string> = {
  objective:
    'I heard some of your answer, but I need to understand the main objective. What were you specifically trying to accomplish?',
  actions:
    "Thanks for sharing. Can you tell me more about the specific actions you took? I need at least three key steps you followed.",
  obstacles:
    "That's helpful. What obstacles or challenges did you face along the way?",
  outcome:
    'Almost there! What was the final outcome or result of your actions?',
  roleClarity:
    'One more thing — can you clarify your specific role in this situation? What was your personal responsibility?',
} as const;

// ---------------------------------------------------------------------------
// Generic fallback prompt (when no slot-specific template exists)
// ---------------------------------------------------------------------------

export const GENERIC_CLARIFICATION_PROMPT =
  "I didn't catch all the details I need. Could you tell me more about {slotName}?";

// ---------------------------------------------------------------------------
// Multi-slot follow-up template (when multiple slots are missing)
// ---------------------------------------------------------------------------

export const MULTI_SLOT_PROMPT_PREFIX =
  "Thanks for what you've shared so far. I still need a few more details: ";

export const MULTI_SLOT_PROMPT_JOINER = ' Also, ';

// ---------------------------------------------------------------------------
// Helper: build a follow-up prompt for a list of missing slots
// ---------------------------------------------------------------------------

export function buildFollowUpPrompt(missingSlots: string[]): string {
  if (missingSlots.length === 0) {
    return '';
  }

  if (missingSlots.length === 1) {
    const slot = missingSlots[0];
    return (
      SLOT_PROMPT_TEMPLATES[slot] ??
      GENERIC_CLARIFICATION_PROMPT.replace('{slotName}', slot)
    );
  }

  // Multiple missing slots — combine prompts
  const prompts = missingSlots.map((slot) => {
    const template = SLOT_PROMPT_TEMPLATES[slot];
    if (template) {
      // Use a lowercased version for joining
      return template.charAt(0).toLowerCase() + template.slice(1);
    }
    return GENERIC_CLARIFICATION_PROMPT.replace('{slotName}', slot);
  });

  return MULTI_SLOT_PROMPT_PREFIX + prompts.join(MULTI_SLOT_PROMPT_JOINER);
}
