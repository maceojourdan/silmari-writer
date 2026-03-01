/**
 * SlotExtractor - Transforms transcribed text into structured slot-value
 * objects by mapping entities into defined slots.
 *
 * Resource: cfg-h5v9 (transformer)
 * Path: 318-complete-voice-answer-advances-workflow
 *
 * Uses deterministic parsing rules (stub for MVP). Will be replaced
 * with LLM-based extraction in a future path.
 */

import { PartialSlotDataSchema } from '@/server/data_structures/VoiceInteractionContext';
import type {
  QuestionTypeDefinition,
  PartialSlotData,
} from '@/server/data_structures/VoiceInteractionContext';
import { VoiceErrors } from '@/server/error_definitions/VoiceErrors';

// ---------------------------------------------------------------------------
// Pattern-based slot extractors
// ---------------------------------------------------------------------------

const SLOT_EXTRACTORS: Record<
  string,
  (transcript: string) => string | string[] | null
> = {
  objective(transcript: string): string | null {
    const patterns = [
      /(?:my )?(?:objective|goal|aim|purpose) (?:was|is) (?:to )?(.+?)(?:\.|$)/i,
      /(?:i )?(?:wanted|needed|tried) to (.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = transcript.match(pattern);
      if (match?.[1]) return match[1].trim();
    }
    return null;
  },

  actions(transcript: string): string[] | null {
    const patterns = [
      /(?:i )?(?:took|did|performed|made) (?:these |the following )?(?:actions?|steps?):?\s*(.+?)(?:\.|$)/i,
      /(?:actions?|steps?):?\s*(.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = transcript.match(pattern);
      if (match?.[1]) {
        const actions = match[1]
          .split(/,|;| and /)
          .map((a) => a.trim())
          .filter((a) => a.length > 0);
        if (actions.length > 0) return actions;
      }
    }
    return null;
  },

  obstacles(transcript: string): string[] | null {
    const patterns = [
      /(?:obstacle|challenge|difficulty|problem|issue)s? (?:was|were|included?):?\s*(.+?)(?:\.|$)/i,
      /(?:i )?(?:faced|encountered|dealt with):?\s*(.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = transcript.match(pattern);
      if (match?.[1]) {
        const obstacles = match[1]
          .split(/,|;| and /)
          .map((o) => o.trim())
          .filter((o) => o.length > 0);
        if (obstacles.length > 0) return obstacles;
      }
    }
    return null;
  },

  outcome(transcript: string): string | null {
    const patterns = [
      /(?:the )?(?:outcome|result|end result) (?:was|is):?\s*(.+?)(?:\.|$)/i,
      /(?:we |i )?(?:achieved|accomplished|delivered|resulted in):?\s*(.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = transcript.match(pattern);
      if (match?.[1]) return match[1].trim();
    }
    return null;
  },

  roleClarity(transcript: string): string | null {
    const patterns = [
      /(?:my )?(?:role|responsibility|position) (?:was|is):?\s*(.+?)(?:\.|$)/i,
      /(?:i was |i am )?(?:responsible for|in charge of|the lead on|leading):?\s*(.+?)(?:\.|$)/i,
    ];
    for (const pattern of patterns) {
      const match = transcript.match(pattern);
      if (match?.[1]) return match[1].trim();
    }
    return null;
  },
};

// ---------------------------------------------------------------------------
// SlotExtractor
// ---------------------------------------------------------------------------

export const SlotExtractor = {
  /**
   * Extracts slot values from transcript text using deterministic parsing
   * rules matched to the question type's slot definitions.
   *
   * @param transcript - The transcribed text from spoken answer
   * @param questionType - The question type definition with slot schemas
   * @returns PartialSlotData with extracted slot-value pairs
   * @throws VoiceError(TRANSFORMATION_FAILED) if input is malformed
   */
  extract(
    transcript: string,
    questionType: QuestionTypeDefinition,
  ): PartialSlotData {
    // Input validation
    if (!transcript || typeof transcript !== 'string' || transcript.trim() === '') {
      throw VoiceErrors.TRANSFORMATION_FAILED(
        'Cannot extract slots from empty or invalid transcript',
      );
    }

    if (!questionType || !questionType.slots) {
      throw VoiceErrors.TRANSFORMATION_FAILED(
        'Cannot extract slots without valid question type definition',
      );
    }

    const slots: PartialSlotData['slots'] = [];

    for (const slotDef of questionType.slots) {
      const extractor = SLOT_EXTRACTORS[slotDef.name];

      if (extractor) {
        const value = extractor(transcript);
        if (value !== null) {
          slots.push({ name: slotDef.name, value });
        }
      } else {
        // Fallback: check if transcript contains the slot name keyword
        const lowerTranscript = transcript.toLowerCase();
        if (lowerTranscript.includes(slotDef.name.toLowerCase())) {
          const value = slotDef.type === 'string_array'
            ? [transcript.trim()]
            : transcript.trim();
          slots.push({ name: slotDef.name, value });
        }
      }
    }

    // If no slots could be extracted, still return a valid structure
    // with the transcript assigned to the first required slot
    if (slots.length === 0) {
      const firstRequired = questionType.minimumRequiredSlots[0];
      if (firstRequired) {
        const def = questionType.slots.find((s) => s.name === firstRequired);
        const value = def?.type === 'string_array'
          ? [transcript.trim()]
          : transcript.trim();
        slots.push({ name: firstRequired, value });
      }
    }

    const result: PartialSlotData = { slots };

    // Validate against Zod schema
    const parsed = PartialSlotDataSchema.safeParse(result);
    if (!parsed.success) {
      throw VoiceErrors.TRANSFORMATION_FAILED(
        `Extracted data failed schema validation: ${parsed.error.issues.map((i) => i.message).join(', ')}`,
      );
    }

    return parsed.data;
  },
} as const;
