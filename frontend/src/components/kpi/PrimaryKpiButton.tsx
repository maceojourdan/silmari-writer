'use client';

/**
 * PrimaryKpiButton - Captures user primary KPI action (e.g., purchase).
 *
 * Resource: ui-w8p2 (component)
 * Path: 339-record-primary-kpi-analytics-event
 *
 * On click:
 *   1. Validate via KpiActionVerifier
 *   2. If invalid → show error, do NOT call API
 *   3. If valid → call recordPrimaryKpi()
 *   4. On success → invoke onRecorded callback
 */

import { useState } from 'react';
import { recordPrimaryKpi } from '@/api_contracts/recordPrimaryKpi';
import type { RecordPrimaryKpiApiResponse } from '@/api_contracts/recordPrimaryKpi';
import { Button } from '@/components/ui/button';
import { validateKpiAction } from '@/verifiers/KpiActionVerifier';

export interface PrimaryKpiButtonProps {
  userId: string;
  actionType: string;
  metadata?: Record<string, unknown>;
  onRecorded?: (response: RecordPrimaryKpiApiResponse) => void;
}

export default function PrimaryKpiButton({
  userId,
  actionType,
  metadata = {},
  onRecorded,
}: PrimaryKpiButtonProps) {
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [isRecorded, setIsRecorded] = useState(false);

  const handleClick = async () => {
    setError(null);

    // Step 1: Client-side validation
    const validation = validateKpiAction(userId, actionType, metadata);
    if (!validation.valid) {
      setError(validation.errors.join(', '));
      return;
    }

    // Step 2: Call API contract
    setIsLoading(true);
    try {
      const result = await recordPrimaryKpi(validation.payload);
      setIsRecorded(true);
      onRecorded?.(result);
    } catch (err) {
      const message = err instanceof Error ? err.message : 'An unexpected error occurred';
      setError(message);
    } finally {
      setIsLoading(false);
    }
  };

  if (isRecorded) {
    return (
      <div className="flex items-center gap-2 text-primary" data-testid="kpi-success">
        <span>KPI action recorded successfully.</span>
      </div>
    );
  }

  return (
    <div className="flex flex-col gap-2">
      <Button
        className="w-fit"
        onClick={handleClick}
        disabled={isLoading}
        aria-label="Record KPI Action"
        data-testid="kpi-button"
      >
        {isLoading ? 'Recording...' : 'Record KPI'}
      </Button>

      {error && (
        <div className="text-sm text-destructive" role="alert" data-testid="kpi-error">
          {error}
        </div>
      )}
    </div>
  );
}
