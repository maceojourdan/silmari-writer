"""FastAPI application with in-memory stores for TDD development."""

import os
import uuid
from datetime import datetime
from typing import Optional

from fastapi import FastAPI, File, HTTPException, UploadFile
from pydantic import BaseModel, Field

# Constants
UPLOAD_DIR = "./uploads"

# Allowed content types for file uploads
ALLOWED_CONTENT_TYPES = {
    # Audio types for transcription
    "audio/webm",
    "audio/mpeg",
    "audio/mp3",
    "audio/wav",
    "audio/ogg",
    "audio/flac",
    # Document types
    "text/plain",
    "application/json",
    "application/pdf",
}

# Pydantic Models


class FileMetadata(BaseModel):
    """Metadata for uploaded files."""

    id: str
    filename: str
    content_type: str
    size: int


class Message(BaseModel):
    """A message within a conversation."""

    id: str
    role: str
    content: str
    created_at: datetime = Field(default_factory=datetime.utcnow)
    attachments: list[str] = Field(default_factory=list)


class Conversation(BaseModel):
    """A conversation containing messages."""

    id: str
    title: str
    created_at: datetime = Field(default_factory=datetime.utcnow)
    updated_at: datetime = Field(default_factory=datetime.utcnow)
    messages: list[Message] = Field(default_factory=list)


# In-memory stores for development/testing
file_store: dict[str, FileMetadata] = {}
conversation_store: dict[str, Conversation] = {}


# FastAPI Application
app = FastAPI(
    title="Silmari Writer API",
    description="A writing assistant application with AI-powered features",
    version="0.1.0",
)


@app.get("/health")
async def health_check() -> dict[str, str]:
    """Health check endpoint."""
    return {"status": "healthy"}


@app.get("/")
async def root() -> dict[str, str]:
    """Root endpoint."""
    return {"message": "Silmari Writer API"}


@app.post("/api/files/upload", status_code=201, response_model=FileMetadata)
async def upload_file(file: UploadFile = File(...)) -> FileMetadata:
    """Upload a file and store its metadata.

    Accepts multipart/form-data with a file field. Validates the file,
    stores it to the uploads directory, and returns file metadata.
    """
    # Read file content to determine actual size
    content = await file.read()
    file_size = len(content)

    # Validate empty file
    if file_size == 0:
        raise HTTPException(status_code=400, detail="Empty file not allowed")

    # Validate content type
    content_type = file.content_type or "application/octet-stream"
    if content_type not in ALLOWED_CONTENT_TYPES:
        raise HTTPException(
            status_code=400,
            detail=f"Invalid content type: {content_type}. Allowed types: {', '.join(sorted(ALLOWED_CONTENT_TYPES))}"
        )

    # Generate unique ID
    file_id = str(uuid.uuid4())

    # Create uploads directory if it doesn't exist
    os.makedirs(UPLOAD_DIR, exist_ok=True)

    # Store file to disk with UUID-based name
    file_path = os.path.join(UPLOAD_DIR, file_id)
    with open(file_path, "wb") as f:
        f.write(content)

    # Create metadata
    metadata = FileMetadata(
        id=file_id,
        filename=file.filename or "unknown",
        content_type=content_type,
        size=file_size,
    )

    # Store metadata
    file_store[file_id] = metadata

    return metadata


@app.get("/api/files/{file_id}", response_model=FileMetadata)
async def get_file_metadata(file_id: str) -> FileMetadata:
    """Retrieve file metadata by ID.

    Returns the metadata for a previously uploaded file.
    """
    if file_id not in file_store:
        raise HTTPException(status_code=404, detail="Resource not found")

    return file_store[file_id]
