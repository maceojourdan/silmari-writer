/**
 * DraftDocumentStructure - Defines the ordered section structure used to
 * organize confirmed claims into a structured draft document.
 *
 * Resource: cfg-d2q3 (common_structure)
 * Path: 325-generate-draft-from-confirmed-claims
 */

import { z } from 'zod';

// ---------------------------------------------------------------------------
// Draft Section Enum — ordered sections for the document
// ---------------------------------------------------------------------------

export const DRAFT_SECTIONS = ['context', 'actions', 'outcome'] as const;

export type DraftSection = (typeof DRAFT_SECTIONS)[number];

export const DraftSectionSchema = z.enum(DRAFT_SECTIONS);

// ---------------------------------------------------------------------------
// DraftDocumentStructure — static utilities for section management
// ---------------------------------------------------------------------------

export const DraftDocumentStructure = {
  /**
   * Returns the ordered list of required sections.
   */
  getRequiredSections(): readonly DraftSection[] {
    return DRAFT_SECTIONS;
  },

  /**
   * Validates whether a string is a valid DraftSection.
   */
  isValidSection(section: string): section is DraftSection {
    return (DRAFT_SECTIONS as readonly string[]).includes(section);
  },

  /**
   * Returns the display label for a section.
   */
  getSectionLabel(section: DraftSection): string {
    const labels: Record<DraftSection, string> = {
      context: 'Context',
      actions: 'Actions',
      outcome: 'Outcome',
    };
    return labels[section];
  },

  /**
   * Returns the sort index for a section (for ordering).
   */
  getSectionOrder(section: DraftSection): number {
    return DRAFT_SECTIONS.indexOf(section);
  },
} as const;
