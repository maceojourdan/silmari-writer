# PATH: store-session-metrics-on-pipeline-run

**Layer:** 3 (Function Path)
**Priority:** P1
**Version:** 1

## Trigger

Scheduled or event-driven metrics pipeline executes for a completed session

## Resource References

| UUID | Name | Role in this path |
|------|------|-------------------|
| `mq-r4z8` | backend_process_chain | Orchestrates the ordered execution of the metrics computation workflow |
| `db-d3w8` | data_access_object | Retrieves session data and persists computed metrics |
| `db-f8n5` | data_structure | Represents session, event, and metrics storage schemas |
| `db-j6x9` | backend_verifier | Validates required fields and metric integrity before persistence |
| `db-l1c3` | backend_error_definitions | Defines structured errors for missing data, invalid state, and persistence failures |
| `cfg-q9c5` | backend_logging | Logs pipeline execution status and persistence outcomes |

## Steps

1. **Trigger metrics process chain**
   - Input: Completed session identifier emitted to backend_process_chain (mq-r4z8)
   - Process: Initiate the metrics computation workflow for the specified completed session
   - Output: Metrics computation job context containing session identifier
   - Error: If session identifier is missing or malformed, raise error defined in backend_error_definitions (db-l1c3) and abort processing

2. **Load session and event data**
   - Input: Session identifier from job context; data retrieved via data_access_object (db-d3w8) from data_structure (db-f8n5)
   - Process: Fetch session core data (timestamps, status) and associated event records required to compute metrics
   - Output: Aggregated session dataset including timestamps and event stream
   - Error: If session is not found or not marked completed, raise error via backend_error_definitions (db-l1c3) and terminate without storing metrics

3. **Compute session metrics**
   - Input: Aggregated session dataset
   - Process: Calculate time-to-first-draft, completion rate, confirmation rate, signal density, and drop-off based on session timestamps and event patterns
   - Output: Session metrics object containing all computed metric values
   - Error: If required data fields are missing or invalid, validate using backend_verifier (db-j6x9) and raise appropriate error from backend_error_definitions (db-l1c3)

4. **Persist metrics record**
   - Input: Session metrics object; persistence via data_access_object (db-d3w8) into data_structure (db-f8n5)
   - Process: Store or update the metrics record associated with the session in the database
   - Output: Persisted metrics record linked to the completed session
   - Error: If database write fails, log via backend_logging (cfg-q9c5) and raise persistence error from backend_error_definitions (db-l1c3)

5. **Mark metrics pipeline success**
   - Input: Persisted metrics record confirmation
   - Process: Record successful completion of the metrics pipeline execution for observability and downstream consumers
   - Output: System state reflecting successful metrics storage for the session
   - Error: If confirmation cannot be recorded, log via backend_logging (cfg-q9c5) and raise operational error from backend_error_definitions (db-l1c3)

## Terminal Condition

Session metrics record exists in the database containing time-to-first-draft, completion rate, confirmation rate, signal density, and drop-off for the completed session

## Feedback Loops

None — strictly linear.
