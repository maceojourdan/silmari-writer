# Phase 05: The system must maintain and enhance existing voic...

## Requirements

### REQ_004: The system must maintain and enhance existing voice input im

The system must maintain and enhance existing voice input implementation using MediaRecorder, Vercel Blob storage, and OpenAI Whisper API

#### REQ_004.1: Capture audio using browser MediaRecorder API with automatic

Capture audio using browser MediaRecorder API with automatic MIME type detection (webm for Chrome/Firefox, mp4 for Safari)

##### Testable Behaviors

1. MediaRecorder successfully initializes when user clicks Record button
2. Microphone permission request is displayed and handled (allow/deny scenarios)
3. MIME type detection correctly identifies 'audio/webm' for Chrome/Firefox browsers
4. MIME type detection correctly identifies 'audio/mp4' for Safari browsers
5. Falls back to 'audio/webm' when no supported MIME type is detected
6. Audio data chunks are collected via ondataavailable event handler
7. Recording timer displays elapsed time in MM:SS format, updating every second
8. Recording automatically stops at MAX_RECORDING_TIME_MS (5 minutes / 300 seconds)
9. Recording indicator (red pulsing dot) is visible during active recording
10. Stop button properly triggers MediaRecorder.stop() and stream track cleanup
11. Audio blob is created from collected chunks with correct MIME type on stop
12. MediaStream tracks are stopped to release microphone when recording ends
13. Error state is set and user-friendly message displayed when microphone access denied
14. Component properly cleans up all resources (timers, streams, URLs) on unmount
15. Reset functionality clears all state and releases resources for re-recording

#### REQ_004.2: Upload recorded audio blob to Vercel Blob storage to bypass 

Upload recorded audio blob to Vercel Blob storage to bypass 4.5MB serverless function payload limit (up to 25MB supported)

##### Testable Behaviors

1. Client-side validation rejects files exceeding MAX_FILE_SIZE_BYTES (25MB)
2. TranscriptionError with code 'FILE_TOO_LARGE' thrown for oversized files
3. FormData is correctly constructed with file blob and timestamped filename
4. File extension is correctly determined from MIME type (mp4 vs webm)
5. Filename format follows pattern: recording-{timestamp}.{extension}
6. POST request to /api/upload endpoint includes FormData body
7. Server validates BLOB_READ_WRITE_TOKEN environment variable exists
8. Server validates file size does not exceed 25MB limit
9. Vercel Blob put() is called with 'public' access and token
10. Successful upload returns { url: blob.url } response
11. Upload errors return { error, code } with appropriate HTTP status
12. TranscriptionError with code 'UPLOAD_ERROR' thrown on failure
13. retryable flag is set to true for network errors, false for validation errors
14. Blob URL is returned for subsequent transcription API call

#### REQ_004.3: Call /api/transcribe endpoint with Vercel Blob URL for Whisp

Call /api/transcribe endpoint with Vercel Blob URL for Whisper transcription

##### Testable Behaviors

1. POST request sent to /api/transcribe with Content-Type: application/json
2. Request body includes blobUrl (required) and optional language parameter
3. TranscriptionOptions.language is included in payload when provided
4. Network errors throw TranscriptionError with code 'NETWORK' and retryable: true
5. Response JSON is parsed and checked for success/failure
6. Failed responses throw TranscriptionError with server-provided code and message
7. Successful responses return data.text as the transcribed string
8. retryable flag from server response is preserved in thrown errors
9. API call properly handles missing or malformed response bodies

#### REQ_004.4: Process audio through OpenAI Whisper API using whisper-1 mod

Process audio through OpenAI Whisper API using whisper-1 model with exponential backoff retry logic

##### Testable Behaviors

1. OPENAI_API_KEY environment variable is validated before processing
2. Blob URL is fetched and converted to ArrayBuffer
3. Content-Type header from blob response is captured for file type validation
4. File size is validated against 25MB limit server-side
5. File type is validated against SUPPORTED_AUDIO_TYPES map
6. OpenAI client is instantiated with validated API key
7. Audio buffer is converted to File using openai toFile() utility
8. Filename includes proper extension based on content type mapping
9. openai.audio.transcriptions.create() called with whisper-1 model
10. Optional language parameter is passed to Whisper API when provided
11. Rate limit errors (429) trigger retry with RATE_LIMIT_BASE_DELAY_MS (10s) base
12. Network/server errors (500-504) trigger retry with BASE_RETRY_DELAY_MS (2s) base
13. Exponential backoff doubles delay on each retry: delay = base * 2^retries
14. Maximum of MAX_RETRIES (3) retry attempts before final failure
15. 401 errors throw TranscriptionError with 'INVALID_API_KEY' code, non-retryable
16. Retry logging includes attempt number, delay, and error code
17. Final transcription.text is extracted and returned on success

#### REQ_004.5: Delete temporary blob from Vercel Blob storage after success

Delete temporary blob from Vercel Blob storage after successful transcription and return text with isVoiceTranscription flag

##### Testable Behaviors

1. Blob deletion is attempted after successful Whisper transcription
2. BLOB_READ_WRITE_TOKEN is validated before deletion attempt
3. Vercel Blob del(blobUrl, { token }) is called to remove temporary file
4. Blob deletion failure is logged but does not fail the transcription request
5. Transcription text is returned in response: { text: string }
6. Blob deletion is also attempted on transcription failure (cleanup on error)
7. Blob deletion errors are logged with console.warn for monitoring
8. Frontend receives text and creates message with isVoiceTranscription: true flag
9. Message is added to conversation store via addMessage() action
10. isVoiceTranscription flag is preserved in Message interface
11. Auto-send behavior triggers when isVoiceTranscription is true (if configured)
12. UI can distinguish voice-originated messages from typed messages


## Success Criteria

- [ ] All tests pass
- [ ] All behaviors implemented
- [ ] Code reviewed