/**
 * RecallModule - Frontend module controlling state detection and RECALL UI orchestration.
 *
 * Resource: ui-v3n6 (module)
 * Path: 303-display-recall-state-with-record-button-and-progress-indicator
 *
 * Manages:
 * - Application state resolution from prop or session store
 * - Fallback to SAFE_DEFAULT on invalid/missing state
 * - Error logging via frontendLogger (cfg-r3d7)
 * - React context provision for resolved state
 */

'use client';

import { useState, useEffect, createContext, useContext } from 'react';
import { frontendLogger } from '@/logging/index';
import { UiErrors } from '@/server/error_definitions/UiErrors';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type AppState = 'INIT' | 'ORIENT' | 'RECALL' | 'SAFE_DEFAULT';

export interface AppStateContext {
  state: AppState;
}

export interface RecallModuleProps {
  initialState: string;
}

// ---------------------------------------------------------------------------
// Context
// ---------------------------------------------------------------------------

const RecallStateContext = createContext<AppStateContext>({ state: 'SAFE_DEFAULT' });

export function useRecallState(): AppStateContext {
  return useContext(RecallStateContext);
}

// ---------------------------------------------------------------------------
// Valid states set
// ---------------------------------------------------------------------------

const VALID_STATES = new Set<string>(['INIT', 'ORIENT', 'RECALL', 'SAFE_DEFAULT']);

function resolveState(initialState: unknown): AppState {
  if (!initialState || typeof initialState !== 'string' || !VALID_STATES.has(initialState)) {
    return 'SAFE_DEFAULT';
  }
  return initialState as AppState;
}

// ---------------------------------------------------------------------------
// Hook
// ---------------------------------------------------------------------------

/**
 * React hook managing the Recall module state resolution.
 *
 * On mount, resolves state from the provided initialState prop.
 * If falsy/unknown, falls back to SAFE_DEFAULT and logs UI_STATE_NOT_FOUND.
 */
export function useRecallModule(props: RecallModuleProps): AppStateContext {
  const resolved = resolveState(props.initialState);

  const [state] = useState<AppState>(() => {
    if (resolved === 'SAFE_DEFAULT' && props.initialState !== 'SAFE_DEFAULT') {
      frontendLogger.error(
        'UI_STATE_NOT_FOUND',
        UiErrors.StateNotFound(`Could not resolve state from: ${String(props.initialState)}`),
        { module: 'RecallModule', action: 'resolveState' },
      );
    }
    return resolved;
  });

  return { state };
}

// ---------------------------------------------------------------------------
// Provider Component
// ---------------------------------------------------------------------------

export function RecallModuleProvider({
  initialState,
  children,
}: RecallModuleProps & { children: React.ReactNode }) {
  const context = useRecallModule({ initialState });

  return (
    <RecallStateContext.Provider value={context}>
      {children}
    </RecallStateContext.Provider>
  );
}
