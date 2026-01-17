# Phase 03: The system must integrate OpenAI Image Creation AP...

## Requirements

### REQ_002: The system must integrate OpenAI Image Creation API using gp

The system must integrate OpenAI Image Creation API using gpt-image-1.5 model with full parameter support

#### REQ_002.1: Implement POST requests to https://api.openai.com/v1/images/

Implement POST requests to https://api.openai.com/v1/images/generations with proper authentication and error handling

##### Testable Behaviors

1. POST requests are sent to https://api.openai.com/v1/images/generations with Content-Type: application/json header
2. Authorization header includes Bearer token with OPENAI_API_KEY from environment variables
3. Request body includes required fields: model, prompt, and optional fields: n, size, quality, output_format, background
4. Prompt length validation enforces 32K character limit for GPT Image models
5. Request timeout is configurable with default of 120 seconds for image generation
6. Rate limit errors (429) trigger exponential backoff retry logic with maximum 3 attempts using 10s base delay
7. API errors return structured ToolError responses with code, message, retryable status, and suggestedAction
8. Network errors are caught and wrapped in consistent ToolError format
9. Request logging captures prompt (truncated to 100 chars), model, size, quality for debugging without exposing sensitive data
10. Successful requests return parsed JSON response with b64_json field extracted
11. Invalid API key returns 401 status with INVALID_API_KEY error code
12. Missing OPENAI_API_KEY environment variable returns 500 with CONFIG_ERROR code

#### REQ_002.2: Support gpt-image-1.5, gpt-image-1, and gpt-image-1-mini mod

Support gpt-image-1.5, gpt-image-1, and gpt-image-1-mini models with DALL-E 3/2 deprecation warnings (May 12, 2026)

##### Testable Behaviors

1. Default model is gpt-image-1.5 for production quality output when no model specified
2. gpt-image-1-mini is selectable when cost optimization is explicitly requested (approximately 80% cheaper)
3. gpt-image-1 is available as standard tier option between mini and 1.5
4. Model parameter accepts only valid values: 'gpt-image-1.5', 'gpt-image-1', 'gpt-image-1-mini'
5. Invalid model values are rejected with 400 status and descriptive error message listing valid options
6. DALL-E 3 model requests return 400 with deprecation warning: 'dall-e-3 is deprecated as of May 12, 2026. Please use gpt-image-1.5 instead.'
7. DALL-E 2 model requests return 400 with deprecation warning: 'dall-e-2 is deprecated as of May 12, 2026. Please use gpt-image-1 or gpt-image-1-mini instead.'
8. Cost estimation is calculated and returned based on model and quality combination before execution
9. Model capabilities are validated against requested parameters (all models support all sizes and background options)
10. Model usage is logged for cost tracking with model name, quality, and timestamp

#### REQ_002.3: Handle base64 response format (GPT Image models always retur

Handle base64 response format (GPT Image models always return base64, never URLs)

##### Testable Behaviors

1. Response JSON is parsed and b64_json field is extracted from response.data[0].b64_json
2. Base64 string is validated using regex pattern /^[A-Za-z0-9+/]+=*$/ before processing
3. Invalid base64 responses trigger ImageGenerationError with INVALID_RESPONSE code and response preview for debugging
4. Multiple images (n > 1) are handled by mapping through data array and extracting each b64_json
5. Revised prompt is extracted from response.data[0].revised_prompt if present and returned to caller
6. Empty, null, or undefined b64_json field triggers error with message 'No image data in response'
7. Response parsing handles malformed JSON gracefully with try-catch and descriptive error
8. Large base64 strings (up to 10MB for high quality images) are processed without memory issues using streaming if needed
9. Response metadata (model used, created timestamp) is extracted and logged for monitoring
10. Parsing duration is measured and logged for performance monitoring

#### REQ_002.4: Convert base64 responses to image buffers and persist to Ver

Convert base64 responses to image buffers and persist to Vercel Blob storage

##### Testable Behaviors

1. Base64 string is decoded to Buffer using Buffer.from(base64, 'base64')
2. Buffer is validated by checking first bytes match expected magic bytes: PNG (89 50 4E 47), JPEG (FF D8 FF), WebP (52 49 46 46)
3. Image buffer is uploaded to Vercel Blob storage using @vercel/blob put() function with public access
4. Generated blob URL is returned as permanent URL for image display and future access
5. Filename is generated with pattern: 'generated-image-{timestamp}-{index}.{format}' (e.g., 'generated-image-1705432800000-0.png')
6. Content-Type header is set correctly based on output_format: 'image/png', 'image/jpeg', or 'image/webp'
7. Upload errors are caught and return ImageStorageError with UPLOAD_FAILED code and retry suggestion
8. Multiple images are stored individually with indexed filenames using Promise.all for parallel uploads
9. Image metadata (prompt hash, model, quality, generation timestamp, size in bytes) is stored in Vercel Blob metadata
10. BLOB_READ_WRITE_TOKEN environment variable is validated before upload attempt
11. Upload size is validated against Vercel Blob limits before attempting storage

#### REQ_002.5: Support all gpt-image-1.5 parameters: size (1024x1024, 1536x

Support all gpt-image-1.5 parameters: size (1024x1024, 1536x1024, 1024x1536, auto), quality (low/medium/high), output_format (png/jpeg/webp), background (auto/transparent/opaque), n (1-10 images)

##### Testable Behaviors

1. Size parameter accepts values: '1024x1024' (square), '1536x1024' (landscape), '1024x1536' (portrait), 'auto' with default '1024x1024'
2. Quality parameter accepts values: 'low', 'medium', 'high' with default 'high'
3. Output format parameter accepts values: 'png', 'jpeg', 'webp' with default 'png'
4. Background parameter accepts values: 'auto', 'transparent', 'opaque' with default 'auto'
5. N parameter accepts integers 1-10 with default 1, values outside range return validation error
6. Transparent background with jpeg format triggers warning and auto-switches to png (jpeg doesn't support transparency)
7. All parameters are validated by Zod schema before API call with descriptive error messages
8. UI provides intuitive controls for each parameter with previews and descriptions
9. Parameter combinations are validated for compatibility (e.g., transparent + png = valid)
10. All parameter values are correctly passed to OpenAI API request body


## Success Criteria

- [ ] All tests pass
- [ ] All behaviors implemented
- [ ] Code reviewed