---
date: 2026-01-16T15:15:57-05:00
researcher: Claude
git_commit: 3e43ed943feed5d3bb476a4eeb254d68c9802049
branch: main
repository: silmari-writer
topic: "OpenAI API Tools (Deep Research, Image Creation, Document Generation) and Voice-Enabled Integration"
tags: [research, openai, deep-research, dall-e, image-generation, document-generation, voice, transcription, tool-routing]
status: complete
last_updated: 2026-01-16
last_updated_by: Claude
---

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                         SILMARI WRITER RESEARCH                              │
│          OpenAI API Tools & Voice-Enabled Integration Architecture           │
│                                                                              │
│  Status: ✅ Complete                           Date: 2026-01-16              │
└──────────────────────────────────────────────────────────────────────────────┘
```

# Research: OpenAI API Tools & Voice-Enabled Integration

**Date**: 2026-01-16T15:15:57-05:00
**Researcher**: Claude
**Git Commit**: 3e43ed943feed5d3bb476a4eeb254d68c9802049
**Branch**: main
**Repository**: silmari-writer

---

## 📚 Research Question

How can we integrate OpenAI's advanced tools (Deep Research, Image Creation, Document Generation) into the silmari-writer application, and how can users request these tools using plain language through voice input?

---

## 📊 Summary

This research documents three OpenAI API capabilities and analyzes the existing codebase to understand how a voice-enabled tool routing system could be implemented.

### Key Findings

| Capability | OpenAI Support | Implementation Approach |
|------------|----------------|------------------------|
| **Deep Research** | ✅ Native API (`o3-deep-research`, `o4-mini-deep-research`) | Responses API with `web_search_preview` tool |
| **Image Creation** | ✅ Native API (`gpt-image-1.5`, DALL-E 3 deprecated) | Images API, returns base64 |
| **Document Generation** | ❌ No native API | AI generates content → library creates document |
| **Voice Input** | ✅ Existing implementation | MediaRecorder → Whisper API |
| **Tool Routing** | ❌ Not implemented | Requires intent classification layer |

---

## 🎯 Detailed Findings

### 1. OpenAI Deep Research API

```
╔═══════════════════════════════════════════════════════════════════════════════╗
║                              DEEP RESEARCH API                                ║
║                    Autonomous Research Agent via Responses API                ║
╚═══════════════════════════════════════════════════════════════════════════════╝
```

#### Overview

Deep Research is an agentic capability that takes high-level queries and returns structured, citation-rich reports. It autonomously decomposes tasks, performs web searches, executes code, and synthesizes results.

#### Available Models

| Model | Use Case | Context | Max Output |
|-------|----------|---------|------------|
| `o3-deep-research-2025-06-26` | In-depth synthesis, higher quality | 200K tokens | 100K tokens |
| `o4-mini-deep-research-2025-06-26` | Speed-sensitive, latency-critical | 200K tokens | 100K tokens |

#### API Endpoint

```
POST https://api.openai.com/v1/responses
```

#### Request Format

```typescript
const response = await openai.responses.create({
  model: "o3-deep-research-2025-06-26",
  input: [
    { role: "developer", content: [{ type: "input_text", text: "System instructions" }] },
    { role: "user", content: [{ type: "input_text", text: "Research query" }] }
  ],
  reasoning: { summary: "auto" },  // or "detailed"
  tools: [
    { type: "web_search_preview" },
    { type: "code_interpreter" }
  ],
  background: true  // Recommended for long-running tasks
});
```

#### Tool Configuration Options

| Tool | Purpose | Configuration |
|------|---------|---------------|
| `web_search_preview` | Internet search | `domains`, `search_context_size`, `user_location` |
| `code_interpreter` | Execute code | No config needed |
| `file_search` | Search uploaded files | `vector_store_ids` (max 2) |
| `mcp` | Custom data sources | `server_url`, `require_approval` |

#### Response Handling

```typescript
// Final report
const reportText = response.output[-1].content[0].text;

// Citations with URLs
const citations = response.output[-1].content[0].annotations;
citations.forEach(c => console.log(`${c.title}: ${c.url}`));

// Intermediate reasoning steps
response.output.forEach(item => {
  if (item.type === "reasoning") console.log(item.summary);
  if (item.type === "web_search_call") console.log(item.query);
});
```

#### Pricing

| Model | Input Tokens | Output Tokens | Cached Input |
|-------|-------------|---------------|--------------|
| o3-deep-research | $10/1M | $40/1M | $2.50/1M |
| o4-mini-deep-research | $2/1M | $8/1M | $0.50/1M |

**Additional Costs:**
- Web search: $0.01 per call
- Code interpreter: $0.03 per session
- Average cost per query: ~$30 (o3), ~$3 (o4-mini)

#### Important Constraints

- **No interactive clarification**: Unlike ChatGPT, the API doesn't ask follow-up questions
- **Long execution time**: Can take tens of minutes; use `background: true`
- **Background mode**: Requires polling or webhooks for completion

**Sources:**
- [Deep Research Guide](https://platform.openai.com/docs/guides/deep-research)
- [Deep Research Cookbook](https://cookbook.openai.com/examples/deep_research_api/introduction_to_deep_research_api)

---

### 2. OpenAI Image Creation API

```
╔═══════════════════════════════════════════════════════════════════════════════╗
║                              IMAGE CREATION API                               ║
║                    GPT Image Models (DALL-E 3 Deprecated May 2026)            ║
╚═══════════════════════════════════════════════════════════════════════════════╝
```

#### Model Landscape (2026)

| Model | Status | Best For |
|-------|--------|----------|
| `gpt-image-1.5` | ✅ Current (Dec 2025) | Production quality, best overall |
| `gpt-image-1` | ✅ Available | Standard generation |
| `gpt-image-1-mini` | ✅ Available | Cost-optimized (~80% cheaper) |
| `dall-e-3` | ⚠️ Deprecated May 12, 2026 | Legacy support |
| `dall-e-2` | ⚠️ Deprecated May 12, 2026 | Legacy support |

#### API Endpoint

```
POST https://api.openai.com/v1/images/generations
```

#### Request Format

```typescript
const result = await openai.images.generate({
  model: "gpt-image-1.5",
  prompt: "A cute baby sea otter in a sunset",
  n: 1,
  size: "1024x1024",
  quality: "high",
  output_format: "png",
  background: "transparent"  // or "opaque", "auto"
});

// GPT Image models ALWAYS return base64
const imageBytes = Buffer.from(result.data[0].b64_json, "base64");
```

#### Parameter Reference

| Parameter | GPT Image | Values |
|-----------|-----------|--------|
| `size` | ✅ | `1024x1024`, `1536x1024`, `1024x1536`, `auto` |
| `quality` | ✅ | `low`, `medium`, `high` |
| `output_format` | ✅ | `png`, `jpeg`, `webp` |
| `background` | ✅ | `auto`, `transparent`, `opaque` |
| `n` | ✅ | 1-10 images |
| `stream` | ✅ | `true`/`false` (real-time streaming) |
| `partial_images` | ✅ | 0-3 (during streaming) |

#### Pricing

| Model | Low Quality | Medium Quality | High Quality |
|-------|-------------|----------------|--------------|
| gpt-image-1.5 | ~$0.01 | ~$0.04 | ~$0.17 |
| gpt-image-1 | ~$0.02 | ~$0.07 | ~$0.19 |
| gpt-image-1-mini | ~$0.002 | ~$0.01 | ~$0.04 |

#### Key Changes from DALL-E 3

| Feature | DALL-E 3 | GPT Image 1.5 |
|---------|----------|---------------|
| Response format | URL or base64 | **Always base64** |
| Number of images | 1 only | 1-10 |
| Prompt length | 4K chars | 32K chars |
| Streaming | No | Yes |
| Background control | No | Yes |

**Sources:**
- [Image Generation Guide](https://platform.openai.com/docs/guides/image-generation)
- [GPT Image 1.5 Model](https://platform.openai.com/docs/models/gpt-image-1.5)

---

### 3. Document Generation (PDF, XLSX, DOCX)

```
╔═══════════════════════════════════════════════════════════════════════════════╗
║                           DOCUMENT GENERATION                                 ║
║              No Native API - Use AI Content + Document Libraries              ║
╚═══════════════════════════════════════════════════════════════════════════════╝
```

#### Key Finding

**OpenAI does NOT have native document generation APIs.** The recommended pattern is:

```
AI generates content (JSON) → Document library creates file (PDF/DOCX/XLSX)
```

#### Recommended Architecture

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│  User Request   │ ──► │  OpenAI API     │ ──► │ Document Library│
│  (plain text)   │     │  (Structured    │     │ (creates file)  │
│                 │     │   Outputs)      │     │                 │
└─────────────────┘     └─────────────────┘     └─────────────────┘
                              │                        │
                              ▼                        ▼
                        JSON Schema             PDF/DOCX/XLSX
                        Validation              File Output
```

#### Structured Outputs (Foundation Pattern)

```typescript
const response = await openai.chat.completions.create({
  model: "gpt-4o",
  response_format: {
    type: "json_schema",
    json_schema: {
      name: "document_content",
      schema: {
        type: "object",
        properties: {
          title: { type: "string" },
          sections: {
            type: "array",
            items: {
              type: "object",
              properties: {
                heading: { type: "string" },
                content: { type: "string" }
              }
            }
          }
        }
      }
    }
  },
  messages: [{ role: "user", content: "Create a project proposal for..." }]
});

const documentData = JSON.parse(response.choices[0].message.content);
```

#### Recommended Libraries

<details>
<summary><b>Python Libraries</b></summary>

| Library | Format | Best For |
|---------|--------|----------|
| **ReportLab** | PDF | Complex layouts, charts, custom designs |
| **PDFKit** | PDF | HTML/CSS to PDF conversion |
| **python-docx** | DOCX | Word documents, rich text |
| **OpenPyXL** | XLSX | Excel spreadsheets |
| **Docxtemplater** | DOCX/XLSX | Template-based generation |

</details>

<details>
<summary><b>Node.js Libraries</b></summary>

| Library | Format | Best For |
|---------|--------|----------|
| **PDFKit** | PDF | Programmatic PDF generation |
| **jsPDF** | PDF | Client-side PDF |
| **Puppeteer** | PDF | HTML rendering to PDF |
| **docx** | DOCX | Word document creation |
| **ExcelJS** | XLSX | Excel generation |

</details>

#### Template-Based Approach (Docxtemplater)

```javascript
// Create professional template in Word with placeholders
// Template: "Dear {customer_name}, your invoice total is {total}..."

const content = await generateWithOpenAI("Generate invoice content for...");
const doc = new Docxtemplater(templateFile);
doc.setData(content);  // AI-generated JSON
doc.render();
const output = doc.getZip().generate({ type: "nodebuffer" });
```

**Sources:**
- [OpenAI Structured Outputs](https://platform.openai.com/docs/guides/structured-outputs)
- [Docxtemplater](https://docxtemplater.com/)

---

### 4. Current Codebase: Voice/Audio Implementation

```
╔═══════════════════════════════════════════════════════════════════════════════╗
║                         EXISTING VOICE IMPLEMENTATION                         ║
║                 MediaRecorder → Vercel Blob → OpenAI Whisper                  ║
╚═══════════════════════════════════════════════════════════════════════════════╝
```

#### Architecture Overview

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Browser   │ ──► │ Vercel Blob │ ──► │ /api/       │ ──► │  OpenAI     │
│ MediaRecorder│    │   Storage   │     │ transcribe  │     │  Whisper    │
└─────────────┘     └─────────────┘     └─────────────┘     └─────────────┘
      │                                        │                   │
      ▼                                        ▼                   ▼
  audio/webm                            Fetch & Delete        Text Output
  (5 min max)                           (cleanup)
```

#### Key Components

| Component | File | Purpose |
|-----------|------|---------|
| AudioRecorder | `frontend/src/components/chat/AudioRecorder.tsx` | Browser recording UI |
| Transcription Client | `frontend/src/lib/transcription.ts` | Two-step upload/transcribe |
| Upload API | `frontend/src/app/api/upload/route.ts` | Vercel Blob storage |
| Transcribe API | `frontend/src/app/api/transcribe/route.ts` | Whisper API call |

#### Recording Flow

1. **User clicks Record** → `AudioRecorder.tsx:253`
2. **Request microphone** → `navigator.mediaDevices.getUserMedia({ audio: true })`
3. **Create MediaRecorder** with webm/mp4 MIME type detection
4. **Collect chunks** in `ondataavailable` handler
5. **User clicks Stop** → Create Blob from chunks
6. **Upload to Vercel Blob** → Returns blob URL (bypasses 4.5MB serverless limit)
7. **POST to /api/transcribe** with blob URL
8. **Fetch blob, call Whisper** → `openai.audio.transcriptions.create({ model: 'whisper-1' })`
9. **Delete blob, return text**
10. **Auto-send as message** with `isVoiceTranscription=true` flag

#### Configuration

| Setting | Value | Location |
|---------|-------|----------|
| Max recording time | 5 minutes | `AudioRecorder.tsx:7` |
| Max file size | 25 MB | `transcription.ts:4` |
| Retry attempts | 3 | `transcribe/route.ts:8` |
| Rate limit delay | 10s base, exponential | `transcribe/route.ts:10` |
| Network error delay | 2s base, exponential | `transcribe/route.ts:9` |

---

### 5. Current Codebase: Tool/Function Patterns

```
╔═══════════════════════════════════════════════════════════════════════════════╗
║                        CURRENT ARCHITECTURE                                   ║
║               Direct Action Routing (No Intent Detection)                     ║
╚═══════════════════════════════════════════════════════════════════════════════╝
```

#### Key Finding: No Tool Registry or Function Calling

The codebase does **not** implement:
- OpenAI function calling API
- Tool registry or dispatch system
- Natural language intent detection
- Plugin/extension architecture

#### Current Pattern: Direct REST Endpoints

| Endpoint | Purpose | Model |
|----------|---------|-------|
| `/api/generate` | Chat completions | gpt-4o-mini |
| `/api/transcribe` | Audio → text | whisper-1 |
| `/api/upload` | File storage | N/A |
| `/api/analytics` | Telemetry | N/A |

#### Button Action System

User actions are triggered through explicit UI buttons, not natural language:

| Button | Type | Action |
|--------|------|--------|
| Copy | Non-blocking | Clipboard API |
| Regenerate | Blocking | `regenerateMessage()` → `/api/generate` |
| Edit | Blocking | Opens modal, updates store |

**Files:**
- `frontend/src/components/chat/ButtonRibbon.tsx` - Button handlers
- `frontend/src/lib/messageActions.ts` - Message operations
- `frontend/src/lib/store.ts` - Zustand state management

---

### 6. Current Codebase: AI Integration

```
╔═══════════════════════════════════════════════════════════════════════════════╗
║                          AI INTEGRATION ARCHITECTURE                          ║
║                   Direct OpenAI SDK + BAML (Configured, Unused)               ║
╚═══════════════════════════════════════════════════════════════════════════════╝
```

#### OpenAI Integration

- **SDK**: `openai` v6.16.0
- **Pattern**: Per-request client instantiation (no singleton)
- **Streaming**: Not implemented (non-streaming only)

```typescript
// frontend/src/app/api/generate/route.ts
const openai = new OpenAI({ apiKey: process.env.OPENAI_API_KEY });
const completion = await openai.chat.completions.create({
  model: 'gpt-4o-mini',
  messages,
  temperature: 0.7,
  max_tokens: 2000,
});
```

#### BAML Framework (Configured but Unused)

BAML provides type-safe LLM function definitions but is not currently active in routes.

**Configured Clients** (`frontend/src/baml_src/clients.baml`):
- OpenAI: GPT-5, GPT-5-Mini
- Anthropic: Claude Opus 4, Sonnet 4, Haiku
- Fallback chains and retry policies

**Generated Client** (`frontend/src/baml_client/`):
- 16 files with async/sync clients
- Supports streaming via `BamlStreamClient`
- Ready for integration

---

## 🚀 Implementation Architecture: Voice-Enabled Tool Routing

```
╔═══════════════════════════════════════════════════════════════════════════════╗
║                     PROPOSED: VOICE-ENABLED TOOL SYSTEM                       ║
║              Plain Language → Intent Detection → Tool Execution               ║
╚═══════════════════════════════════════════════════════════════════════════════╝
```

### Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                            USER INTERFACE                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│  [🎤 Voice Input]  ────►  AudioRecorder  ────►  Whisper API                │
│  [⌨️ Text Input]   ────►  MessageInput                                     │
└───────────────────────────────┬─────────────────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         INTENT CLASSIFICATION                               │
├─────────────────────────────────────────────────────────────────────────────┤
│  "Research quantum computing trends"     ──►  🔬 DEEP_RESEARCH             │
│  "Create an image of a sunset"           ──►  🎨 IMAGE_GENERATION          │
│  "Generate a PDF report"                 ──►  📄 DOCUMENT_GENERATION       │
│  "Write a story about dragons"           ──►  💬 CHAT_COMPLETION           │
└───────────────────────────────┬─────────────────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           TOOL ROUTER                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│  Tool Registry                          │  Tool Handlers                   │
│  ├── deep_research                      │  ├── DeepResearchHandler         │
│  ├── image_generation                   │  ├── ImageGenerationHandler      │
│  ├── document_generation                │  ├── DocumentGenerationHandler   │
│  └── chat_completion                    │  └── ChatCompletionHandler       │
└───────────────────────────────┬─────────────────────────────────────────────┘
                                │
                                ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                          EXTERNAL SERVICES                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│  OpenAI Responses API  │  OpenAI Images API  │  Document Libraries         │
│  (Deep Research)       │  (gpt-image-1.5)    │  (PDFKit, docx, ExcelJS)    │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Component Design

#### 1. Intent Classifier

```typescript
// frontend/src/lib/intentClassifier.ts

export type ToolIntent =
  | 'deep_research'
  | 'image_generation'
  | 'document_generation'
  | 'chat_completion';

export interface ClassifiedIntent {
  tool: ToolIntent;
  confidence: number;
  extractedParams: Record<string, unknown>;
}

export async function classifyIntent(userMessage: string): Promise<ClassifiedIntent> {
  const response = await openai.chat.completions.create({
    model: 'gpt-4o-mini',
    response_format: { type: 'json_object' },
    messages: [
      {
        role: 'system',
        content: `Classify the user's intent into one of these tools:
          - deep_research: Research queries, fact-finding, analysis requests
          - image_generation: Create images, draw, visualize, artwork
          - document_generation: Create PDF, Word doc, Excel spreadsheet, report
          - chat_completion: General conversation, writing, questions

          Return JSON: { "tool": "<tool_name>", "confidence": 0.0-1.0, "params": {} }`
      },
      { role: 'user', content: userMessage }
    ]
  });

  return JSON.parse(response.choices[0].message.content);
}
```

#### 2. Tool Registry

```typescript
// frontend/src/lib/toolRegistry.ts

export interface ToolDefinition {
  name: string;
  description: string;
  triggerPhrases: string[];
  handler: (params: ToolParams) => Promise<ToolResult>;
  responseType: 'text' | 'image' | 'file';
}

export const toolRegistry: Map<string, ToolDefinition> = new Map([
  ['deep_research', {
    name: 'Deep Research',
    description: 'Autonomous research with citations',
    triggerPhrases: ['research', 'investigate', 'find out about', 'analyze'],
    handler: handleDeepResearch,
    responseType: 'text'
  }],
  ['image_generation', {
    name: 'Image Generation',
    description: 'Create images from descriptions',
    triggerPhrases: ['create image', 'draw', 'generate picture', 'visualize'],
    handler: handleImageGeneration,
    responseType: 'image'
  }],
  ['document_generation', {
    name: 'Document Generation',
    description: 'Create PDF, DOCX, or XLSX files',
    triggerPhrases: ['create document', 'generate report', 'make spreadsheet'],
    handler: handleDocumentGeneration,
    responseType: 'file'
  }]
]);
```

#### 3. Tool Handlers

<details>
<summary><b>Deep Research Handler</b></summary>

```typescript
// frontend/src/lib/tools/deepResearch.ts

export async function handleDeepResearch(params: {
  query: string;
  depth?: 'quick' | 'thorough';
}): Promise<{ text: string; citations: Citation[] }> {

  const response = await fetch('/api/tools/deep-research', {
    method: 'POST',
    body: JSON.stringify({
      model: params.depth === 'thorough'
        ? 'o3-deep-research-2025-06-26'
        : 'o4-mini-deep-research-2025-06-26',
      query: params.query,
      tools: [{ type: 'web_search_preview' }],
      background: true
    })
  });

  // Poll for completion or use webhooks
  const result = await pollForCompletion(response.id);

  return {
    text: result.output[-1].content[0].text,
    citations: result.output[-1].content[0].annotations
  };
}
```

</details>

<details>
<summary><b>Image Generation Handler</b></summary>

```typescript
// frontend/src/lib/tools/imageGeneration.ts

export async function handleImageGeneration(params: {
  prompt: string;
  size?: '1024x1024' | '1536x1024' | '1024x1536';
  quality?: 'low' | 'medium' | 'high';
}): Promise<{ imageUrl: string; revisedPrompt?: string }> {

  const response = await fetch('/api/tools/generate-image', {
    method: 'POST',
    body: JSON.stringify({
      model: 'gpt-image-1.5',
      prompt: params.prompt,
      size: params.size || '1024x1024',
      quality: params.quality || 'high',
      output_format: 'png'
    })
  });

  const result = await response.json();
  const imageBuffer = Buffer.from(result.b64_json, 'base64');

  // Upload to Vercel Blob for persistence
  const blob = await uploadToBlob(imageBuffer, 'generated-image.png');

  return {
    imageUrl: blob.url,
    revisedPrompt: result.revised_prompt
  };
}
```

</details>

<details>
<summary><b>Document Generation Handler</b></summary>

```typescript
// frontend/src/lib/tools/documentGeneration.ts

export async function handleDocumentGeneration(params: {
  type: 'pdf' | 'docx' | 'xlsx';
  contentPrompt: string;
  template?: string;
}): Promise<{ fileUrl: string; filename: string }> {

  // Step 1: Generate structured content with AI
  const content = await generateStructuredContent(params.contentPrompt, params.type);

  // Step 2: Create document with appropriate library
  let fileBuffer: Buffer;
  let filename: string;

  switch (params.type) {
    case 'pdf':
      fileBuffer = await createPDF(content);
      filename = 'document.pdf';
      break;
    case 'docx':
      fileBuffer = await createDOCX(content);
      filename = 'document.docx';
      break;
    case 'xlsx':
      fileBuffer = await createXLSX(content);
      filename = 'spreadsheet.xlsx';
      break;
  }

  // Step 3: Upload to Vercel Blob
  const blob = await uploadToBlob(fileBuffer, filename);

  return { fileUrl: blob.url, filename };
}
```

</details>

### API Routes Structure

```
frontend/src/app/api/
├── generate/route.ts           # Existing chat completion
├── transcribe/route.ts         # Existing voice transcription
├── upload/route.ts             # Existing file upload
├── tools/
│   ├── classify/route.ts       # NEW: Intent classification
│   ├── deep-research/route.ts  # NEW: Deep Research API
│   ├── generate-image/route.ts # NEW: Image generation
│   └── generate-document/route.ts # NEW: Document creation
```

### Message Flow with Tool Routing

```
1. User speaks: "Research the latest AI trends and create a PDF report"
   │
   ▼
2. AudioRecorder captures audio → Whisper transcribes
   │
   ▼
3. Intent Classifier analyzes:
   {
     tool: 'document_generation',
     confidence: 0.92,
     params: {
       type: 'pdf',
       contentSource: 'deep_research',
       topic: 'latest AI trends'
     }
   }
   │
   ▼
4. Tool Router executes:
   a. DeepResearchHandler runs research
   b. DocumentGenerationHandler creates PDF from research
   │
   ▼
5. Response displayed with:
   - Research summary text
   - Download link for PDF
   - Citations from research
```

---

## 🛡️ Implementation Considerations

### Priority Matrix

| Feature | Priority | Effort | Dependencies |
|---------|:--------:|:------:|--------------|
| Intent Classification | 🔴 High | Medium | GPT-4o structured outputs |
| Image Generation | 🔴 High | Low | gpt-image-1.5 API |
| Deep Research | 🟡 Medium | Medium | Responses API, webhooks |
| Document Generation | 🟡 Medium | High | Document libraries |
| Voice trigger words | 🟢 Low | Low | Intent classifier |

### Error Handling

```typescript
// Consistent error responses across tools
interface ToolError {
  code: 'RATE_LIMIT' | 'INVALID_REQUEST' | 'API_ERROR' | 'TIMEOUT';
  message: string;
  retryable: boolean;
  suggestedAction?: string;
}
```

### Cost Management

| Tool | Estimated Cost | Mitigation |
|------|----------------|------------|
| Deep Research (o3) | ~$30/query | Use o4-mini for quick queries |
| Deep Research (o4-mini) | ~$3/query | Default option |
| Image Generation | ~$0.17/image | Cache common requests |
| Document Generation | ~$0.05/doc | Use Structured Outputs |

---

## 📁 Code References

### Existing Voice Implementation
- `frontend/src/components/chat/AudioRecorder.tsx` - Recording component
- `frontend/src/lib/transcription.ts` - Transcription utility
- `frontend/src/app/api/transcribe/route.ts` - Whisper API route
- `frontend/src/app/api/upload/route.ts` - Vercel Blob upload

### Existing AI Integration
- `frontend/src/app/api/generate/route.ts` - Chat completion route
- `frontend/src/lib/api.ts` - API utilities
- `frontend/src/lib/store.ts` - Zustand state management
- `frontend/src/baml_src/clients.baml` - BAML client configs

### State Management
- `frontend/src/lib/types.ts:49-56` - Message type with `isVoiceTranscription` flag
- `frontend/src/lib/store.ts:98-109` - `addMessage()` action

---

## 📚 Historical Context

| Document | Topic | Path |
|----------|-------|------|
| API Endpoints Research | BAML integration plans | `thoughts/searchable/shared/research/2026-01-15-api-endpoints-baml-integration.md` |
| Audio Transcription Plan | TDD implementation | `thoughts/searchable/shared/plans/2026-01-10-tdd-writing-agent-ui-02-audio-transcription.md` |

---

## ❓ Open Questions

1. **Background job handling**: How to manage long-running Deep Research tasks? Webhooks vs polling?
2. **Multi-tool chains**: How to handle "research X and create a document"?
3. **Cost visibility**: Should users see estimated costs before tool execution?
4. **Confidence thresholds**: When should intent classifier ask for clarification?
5. **BAML migration**: Should new tools use BAML for type safety?

---

## 📖 Additional Resources

### OpenAI Documentation
- [Deep Research Guide](https://platform.openai.com/docs/guides/deep-research)
- [Image Generation Guide](https://platform.openai.com/docs/guides/image-generation)
- [Structured Outputs](https://platform.openai.com/docs/guides/structured-outputs)
- [Responses API Reference](https://platform.openai.com/docs/api-reference/responses)

### Document Generation
- [Docxtemplater](https://docxtemplater.com/) - Template-based documents
- [PDFKit](https://pdfkit.org/) - Programmatic PDF generation
- [ExcelJS](https://github.com/exceljs/exceljs) - Excel generation

### Tutorials
- [Deep Research Cookbook](https://cookbook.openai.com/examples/deep_research_api/introduction_to_deep_research_api)
- [GPT Image 1.5 Prompting Guide](https://cookbook.openai.com/examples/multimodal/image-gen-1.5-prompting_guide)
