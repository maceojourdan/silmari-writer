# PATH: return-to-recall-from-review

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User clicks the 'Return to Recall' option on the review screen

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Implements the Review screen UI and handles the 'Return to Recall' user interaction event. |
| `ui-v3n6` | module | Manages the writing flow state and controls which step (Review or Recall) is active and rendered. |
| `cfg-r3d7` | frontend_logging | Records client-side errors such as failed event handling, invalid state transitions, or rendering failures. |

## Steps

1. **Capture return action**
   - Input: User interaction event on the Review screen within frontend component (ui-w8p2)
   - Process: The Review screen component detects the 'Return to Recall' selection and emits a navigation intent to move back to the Recall step.
   - Output: Navigation intent targeting the Recall step within the writing flow module
   - Error: If the click event is not properly bound or the component is unmounted, the navigation intent is not emitted and an error is logged via frontend logging (cfg-r3d7).

2. **Update writing flow state**
   - Input: Navigation intent to return to Recall; current step state from frontend module (ui-v3n6)
   - Process: The writing flow module updates its internal state to set the active step to 'Recall' and mark the Review step as inactive.
   - Output: Updated module state with 'Recall' as the active step
   - Error: If the current flow state is invalid or missing, the module prevents the transition and logs the state inconsistency via frontend logging (cfg-r3d7).

3. **Re-render Recall screen**
   - Input: Updated active step state from frontend module (ui-v3n6)
   - Process: The module conditionally renders the Recall step component and removes the Review component from the visible UI.
   - Output: Recall step component mounted and displayed; Review component unmounted
   - Error: If the Recall component fails to mount, the UI displays a fallback error state and logs the rendering failure via frontend logging (cfg-r3d7).

## Terminal Condition

User sees the Recall step screen with its input interface active and the Review screen no longer visible

## Feedback Loops

None — strictly linear.
