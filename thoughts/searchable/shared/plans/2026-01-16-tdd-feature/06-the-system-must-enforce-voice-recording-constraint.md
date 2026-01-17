# Phase 06: The system must enforce voice recording constraint...

## Requirements

### REQ_005: The system must enforce voice recording constraints with ret

The system must enforce voice recording constraints with retry logic and exponential backoff

#### REQ_005.1: Enforce 5 minute maximum recording duration with visual coun

Enforce 5 minute maximum recording duration with visual countdown timer and automatic stop

##### Testable Behaviors

1. MAX_RECORDING_TIME_MS constant is set to 300000 (5 minutes)
2. Visual countdown timer displays remaining time in MM:SS format during recording
3. Timer color changes to warning (yellow/orange) at 1 minute remaining
4. Timer color changes to critical (red) at 30 seconds remaining
5. Audio and visual warning triggers at 30 seconds remaining
6. Recording automatically stops when timer reaches 0
7. stopRecording() is called via ref to avoid stale closure when auto-stopping
8. Timer interval is cleared on both manual stop and auto-stop
9. MediaStream tracks are stopped to release microphone access
10. User sees toast notification when recording is auto-stopped due to time limit
11. Recording state transitions to 'stopped' after auto-stop
12. Audio blob is still created and passed to onRecordingComplete callback on auto-stop

#### REQ_005.2: Validate 25 MB maximum file size before upload with user-fri

Validate 25 MB maximum file size before upload with user-friendly error messages

##### Testable Behaviors

1. MAX_FILE_SIZE_MB constant is set to 25
2. MAX_FILE_SIZE_BYTES is calculated as MAX_FILE_SIZE_MB * 1024 * 1024 (26214400)
3. Client-side validation in transcription.ts checks audioBlob.size before upload attempt
4. Server-side validation in transcribe/route.ts checks fileBuffer.byteLength after blob fetch
5. TranscriptionError with code 'FILE_TOO_LARGE' is thrown when validation fails
6. Error message includes the actual file size and the limit (e.g., 'File size 28.5MB exceeds 25MB limit')
7. retryable flag is set to false for file size errors (not transient)
8. UI displays human-readable error message with suggestion to record shorter audio
9. Error is displayed before any network request is made (fast feedback)
10. Validation occurs in both client (transcription.ts line 22) and server (route.ts line 63)

#### REQ_005.3: Implement 3 retry attempts for transcription failures with a

Implement 3 retry attempts for transcription failures with attempt tracking and logging

##### Testable Behaviors

1. MAX_RETRIES constant is set to 3
2. transcribeWithRetry function accepts retries parameter starting at 0
3. Only errors with retryable: true trigger retry attempts
4. Each retry attempt is logged with format 'Retry {n}/{MAX_RETRIES} after {delay}ms ({error_code})'
5. Retry counter increments on each recursive call (retries + 1)
6. Function throws after MAX_RETRIES attempts are exhausted
7. Final error includes context that all retries were exhausted
8. Non-retryable errors (INVALID_API_KEY, FILE_TOO_LARGE) throw immediately without retry
9. Successful transcription on retry returns text without additional error
10. Retry attempts are tracked in structured log format for debugging/monitoring

#### REQ_005.4: Apply 10 second base delay with exponential backoff for rate

Apply 10 second base delay with exponential backoff for rate limit errors (HTTP 429) up to 60 second max

##### Testable Behaviors

1. RATE_LIMIT_BASE_DELAY_MS constant is set to 10000 (10 seconds)
2. Maximum delay is capped at 60000ms (60 seconds)
3. Delay calculation uses exponential backoff: baseDelay * 2^retries
4. Retry 1: 10s delay, Retry 2: 20s delay, Retry 3: 40s delay (all under 60s cap)
5. Delay is capped at MAX_RATE_LIMIT_DELAY_MS if calculation exceeds it
6. Rate limit errors are identified by HTTP status 429 or error.code === 'RATE_LIMIT'
7. TranscriptionError with code 'RATE_LIMIT' has retryable: true
8. Delay is applied using await new Promise(resolve => setTimeout(resolve, delay))
9. Log message includes calculated delay: 'Rate limit hit, waiting {delay}ms before retry'
10. Error message to user indicates rate limit and suggests waiting

#### REQ_005.5: Apply 2 second base delay with exponential backoff for netwo

Apply 2 second base delay with exponential backoff for network errors up to 30 second max with jitter

##### Testable Behaviors

1. BASE_RETRY_DELAY_MS constant is set to 2000 (2 seconds)
2. Maximum network retry delay is capped at 30000ms (30 seconds)
3. Delay calculation uses exponential backoff: baseDelay * 2^retries
4. Retry 1: ~2s, Retry 2: ~4s, Retry 3: ~8s (with jitter)
5. Jitter is applied using formula: delay * (0.5 + Math.random()) for ±50% variance
6. Network errors are identified by catch block in fetch or status 502/503/504
7. TranscriptionError with code 'NETWORK' has retryable: true
8. Connection timeout errors are treated as network errors
9. ECONNREFUSED, ETIMEDOUT, ENOTFOUND errors are caught and wrapped
10. Log message includes jittered delay: 'Network error, retrying in {delay}ms (with jitter)'
11. Final error after retries includes suggestion to check network connection


## Success Criteria

- [x] All tests pass (63 voice-related tests passing)
- [x] All behaviors implemented
- [ ] Code reviewed

## Implementation Summary (2026-01-16)

### REQ_005.1: 5-minute max recording with countdown timer
- Added countdown timer showing remaining time (not elapsed)
- Timer color changes: gray (normal) → yellow (≤60s) → red (≤30s)
- Audio warning beep at 30 seconds remaining using Web Audio API
- Toast notification on auto-stop: "Recording stopped - maximum 5 minute limit reached"
- Exported constants: MAX_RECORDING_TIME_MS, MAX_RECORDING_TIME_SECONDS

### REQ_005.2: 25 MB file size validation
- Client and server-side validation
- Error message includes actual size: "File size 28.5MB exceeds 25MB limit. Try recording a shorter audio clip."

### REQ_005.3: 3 retry attempts
- MAX_RETRIES = 3
- Structured logging: "Retry {n}/{MAX_RETRIES} after {delay}ms ({error_code})"
- Final error includes "All 3 retry attempts exhausted" message

### REQ_005.4: 10-second rate limit backoff
- RATE_LIMIT_BASE_DELAY_MS = 10000
- MAX_RATE_LIMIT_DELAY_MS = 60000 (60 second cap)
- Log message: "Rate limit hit, waiting {delay}ms before retry"

### REQ_005.5: 2-second network error backoff with jitter
- BASE_RETRY_DELAY_MS = 2000
- MAX_NETWORK_DELAY_MS = 30000 (30 second cap)
- Jitter applied: delay * (0.5 + Math.random())
- ECONNREFUSED, ETIMEDOUT, ENOTFOUND error handling
- Log message: "Network error, retrying in {delay}ms (with jitter)"
- Final error includes: "Please check your network connection."

### Files Modified
- `frontend/src/components/chat/AudioRecorder.tsx`
- `frontend/src/lib/transcription.ts`
- `frontend/src/app/api/transcribe/route.ts`
- `frontend/__tests__/components/AudioRecorder.test.tsx`
- `frontend/__tests__/lib/transcription.test.ts`
- `frontend/__tests__/api/transcribe.test.ts`