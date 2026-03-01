# PATH: switch-selected-story-before-confirmation

**Layer:** 3 (Function Path)
**Priority:** P0
**Version:** 1

## Trigger

User clicks on a different story in the story selection list before confirming the current selection.

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `ui-w8p2` | component | Handles story selection events, manages selected state, and renders updated UI. |
| `cfg-r3d7` | frontend_logging | Logs client-side errors during event handling, state updates, and rendering. |

## Steps

1. **Capture story selection event**
   - Input: User click event on a story item handled by frontend component (ui-w8p2).
   - Process: The component detects that a story item was clicked and identifies the newly selected story along with the currently selected story from its UI state.
   - Output: Newly selected story identifier and current selected story identifier available in component state context.
   - Error: If the clicked story identifier is missing or invalid, the component ignores the event and logs via frontend_logging (cfg-r3d7).

2. **Evaluate selection change**
   - Input: Newly selected story identifier and current selected story identifier from component state (ui-w8p2).
   - Process: The component compares the two identifiers to determine that a different story is being selected before confirmation.
   - Output: Decision to update selection state to the newly selected story.
   - Error: If the newly selected story matches the current selection, no state change occurs and the component exits without further updates.

3. **Update selected story state**
   - Input: Decision to update selection and component-managed story list state (ui-w8p2).
   - Process: The component updates its internal state so that the previous story's selected flag is set to false and the newly selected story's selected flag is set to true, ensuring only one story is marked as selected.
   - Output: Updated component state where exactly one story is marked as selected.
   - Error: If state update fails due to inconsistent data (e.g., story not found), an error is logged via frontend_logging (cfg-r3d7) and the previous consistent state is retained.

4. **Render updated selection in UI**
   - Input: Updated component state with the new single selected story (ui-w8p2).
   - Process: The component re-renders the story list UI to reflect the updated selection state.
   - Output: User sees the previously selected story deselected and only the newly selected story visually marked as selected.
   - Error: If rendering fails, an error is logged via frontend_logging (cfg-r3d7) and the UI remains in the last successfully rendered state.

## Terminal Condition

The previously selected story is visually deselected and only the newly clicked story is visibly marked as selected in the UI.

## Feedback Loops

None — strictly linear.
