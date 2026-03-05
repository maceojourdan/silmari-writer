'use client';

/**
 * BehavioralQuestionForm - Frontend component where user fills out
 * behavioral question slots and sees status transitions.
 *
 * Resource: ui-w8p2 (component)
 * Path: 296-transition-to-verify-when-minimum-slots-filled
 *
 * On submit:
 *   1. Run frontend verifier (validateMinimumSlots).
 *   2. If valid → call evaluateBehavioralQuestion().
 *   3. On success → display VERIFY badge.
 *   4. On error → display error alert.
 */

import { useBehavioralQuestionModule } from '@/modules/behavioralQuestion/module';
import { Button } from '@/components/ui/button';

export interface BehavioralQuestionFormProps {
  sessionId: string;
  onStatusChange?: (status: 'DRAFT' | 'VERIFY') => void;
}

export default function BehavioralQuestionForm({
  sessionId,
  onStatusChange,
}: BehavioralQuestionFormProps) {
  const {
    draft,
    errors,
    isSubmitting,
    status,
    apiError,
    submit,
    updateField,
  } = useBehavioralQuestionModule(sessionId);

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    await submit();
    if (onStatusChange && status !== 'DRAFT') {
      onStatusChange(status);
    }
  };

  return (
    <form onSubmit={handleSubmit} className="flex flex-col gap-4 p-4">
      {/* Status Badge */}
      <div className="flex items-center gap-2">
        <span
          data-testid="status-badge"
          className={`rounded px-2 py-1 text-xs font-semibold ${
            status === 'VERIFY'
              ? 'bg-primary text-primary-foreground'
              : 'bg-secondary text-secondary-foreground'
          }`}
        >
          {status}
        </span>
      </div>

      {/* Objective */}
      <div className="flex flex-col gap-1">
        <label htmlFor="objective" className="text-sm font-medium">
          Objective
        </label>
        <input
          id="objective"
          type="text"
          value={draft.objective}
          onChange={(e) => updateField('objective', e.target.value)}
          className="rounded border border-input bg-background px-3 py-2 text-sm"
          placeholder="What was the objective or situation?"
        />
        {errors.objective && (
          <span className="text-xs text-destructive">{errors.objective}</span>
        )}
      </div>

      {/* Actions */}
      <div className="flex flex-col gap-1">
        <label className="text-sm font-medium">Actions (min 3)</label>
        {draft.actions.map((action, i) => (
          <div key={i} className="flex gap-2">
            <input
              type="text"
              value={action}
              onChange={(e) => {
                const newActions = [...draft.actions];
                newActions[i] = e.target.value;
                updateField('actions', newActions);
              }}
              className="flex-1 rounded border border-input bg-background px-3 py-2 text-sm"
              placeholder={`Action ${i + 1}`}
            />
            <button
              type="button"
              onClick={() => {
                const newActions = draft.actions.filter((_, idx) => idx !== i);
                updateField('actions', newActions);
              }}
              className="px-2 text-sm text-destructive hover:text-destructive/80"
              aria-label={`Remove action ${i + 1}`}
            >
              Remove
            </button>
          </div>
        ))}
        <button
          type="button"
          onClick={() => updateField('actions', [...draft.actions, ''])}
          className="self-start text-sm text-primary hover:text-primary/80"
          aria-label="Add action"
        >
          + Add Action
        </button>
        {errors.actions && (
          <span className="text-xs text-destructive">{errors.actions}</span>
        )}
      </div>

      {/* Obstacles */}
      <div className="flex flex-col gap-1">
        <label className="text-sm font-medium">Obstacles (min 1)</label>
        {draft.obstacles.map((obstacle, i) => (
          <div key={i} className="flex gap-2">
            <input
              type="text"
              value={obstacle}
              onChange={(e) => {
                const newObstacles = [...draft.obstacles];
                newObstacles[i] = e.target.value;
                updateField('obstacles', newObstacles);
              }}
              className="flex-1 rounded border border-input bg-background px-3 py-2 text-sm"
              placeholder={`Obstacle ${i + 1}`}
            />
            <button
              type="button"
              onClick={() => {
                const newObstacles = draft.obstacles.filter(
                  (_, idx) => idx !== i,
                );
                updateField('obstacles', newObstacles);
              }}
              className="px-2 text-sm text-destructive hover:text-destructive/80"
              aria-label={`Remove obstacle ${i + 1}`}
            >
              Remove
            </button>
          </div>
        ))}
        <button
          type="button"
          onClick={() => updateField('obstacles', [...draft.obstacles, ''])}
          className="self-start text-sm text-primary hover:text-primary/80"
          aria-label="Add obstacle"
        >
          + Add Obstacle
        </button>
        {errors.obstacles && (
          <span className="text-xs text-destructive">{errors.obstacles}</span>
        )}
      </div>

      {/* Outcome */}
      <div className="flex flex-col gap-1">
        <label htmlFor="outcome" className="text-sm font-medium">
          Outcome
        </label>
        <input
          id="outcome"
          type="text"
          value={draft.outcome}
          onChange={(e) => updateField('outcome', e.target.value)}
          className="rounded border border-input bg-background px-3 py-2 text-sm"
          placeholder="What was the result or outcome?"
        />
        {errors.outcome && (
          <span className="text-xs text-destructive">{errors.outcome}</span>
        )}
      </div>

      {/* Role Clarity */}
      <div className="flex flex-col gap-1">
        <label htmlFor="roleClarity" className="text-sm font-medium">
          Role Clarity
        </label>
        <input
          id="roleClarity"
          type="text"
          value={draft.roleClarity}
          onChange={(e) => updateField('roleClarity', e.target.value)}
          className="rounded border border-input bg-background px-3 py-2 text-sm"
          placeholder="What was your specific role?"
        />
        {errors.roleClarity && (
          <span className="text-xs text-destructive">{errors.roleClarity}</span>
        )}
      </div>

      {/* API Error */}
      {apiError && (
        <div
          className="rounded border border-destructive/30 bg-destructive/10 p-2 text-sm text-destructive"
          role="alert"
        >
          {apiError}
        </div>
      )}

      {/* Submit Button */}
      <Button
        type="submit"
        disabled={isSubmitting || status === 'VERIFY'}
        className="w-fit"
        aria-label="Submit for verification"
      >
        {isSubmitting ? 'Submitting...' : 'Submit for Verification'}
      </Button>
    </form>
  );
}
