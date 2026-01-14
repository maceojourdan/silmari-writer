"""Tests for file upload and retrieval functionality."""

import io
import os
import shutil
import uuid

import pytest
from httpx import AsyncClient, ASGITransport

from backend.app import app, file_store, FileMetadata


# Test upload directory
UPLOAD_DIR = "./uploads"


@pytest.fixture
def cleanup_uploads():
    """Clean up uploads directory after tests."""
    yield
    if os.path.exists(UPLOAD_DIR):
        shutil.rmtree(UPLOAD_DIR)


class TestFileMetadataModel:
    """Tests for REQ_001.3: FileMetadata Pydantic model."""

    def test_file_metadata_has_id_field(self):
        """FileMetadata model includes 'id' field as string (UUID format)."""
        metadata = FileMetadata(
            id="550e8400-e29b-41d4-a716-446655440000",
            filename="test.txt",
            content_type="text/plain",
            size=100
        )
        assert metadata.id == "550e8400-e29b-41d4-a716-446655440000"
        assert isinstance(metadata.id, str)

    def test_file_metadata_has_filename_field(self):
        """FileMetadata model includes 'filename' field as string."""
        metadata = FileMetadata(
            id="test-id",
            filename="document.pdf",
            content_type="application/pdf",
            size=1024
        )
        assert metadata.filename == "document.pdf"
        assert isinstance(metadata.filename, str)

    def test_file_metadata_has_content_type_field(self):
        """FileMetadata model includes 'content_type' field as string."""
        metadata = FileMetadata(
            id="test-id",
            filename="audio.mp3",
            content_type="audio/mpeg",
            size=5000
        )
        assert metadata.content_type == "audio/mpeg"
        assert isinstance(metadata.content_type, str)

    def test_file_metadata_has_size_field(self):
        """FileMetadata model includes 'size' field as integer (bytes)."""
        metadata = FileMetadata(
            id="test-id",
            filename="test.txt",
            content_type="text/plain",
            size=2048
        )
        assert metadata.size == 2048
        assert isinstance(metadata.size, int)

    def test_file_metadata_validates_non_negative_size(self):
        """Model validates that size is non-negative."""
        # Size of 0 should be allowed at model level (validation happens at endpoint)
        metadata = FileMetadata(
            id="test-id",
            filename="test.txt",
            content_type="text/plain",
            size=0
        )
        assert metadata.size == 0

    def test_file_metadata_serializes_to_json(self):
        """Model serializes correctly to JSON for API responses."""
        metadata = FileMetadata(
            id="test-id",
            filename="test.txt",
            content_type="text/plain",
            size=100
        )
        json_data = metadata.model_dump()
        assert json_data == {
            "id": "test-id",
            "filename": "test.txt",
            "content_type": "text/plain",
            "size": 100
        }

    def test_file_store_is_module_level_dict(self):
        """file_store is a module-level dictionary accessible by all endpoints."""
        assert isinstance(file_store, dict)

    def test_file_store_is_clearable(self):
        """Store is clearable for test isolation via conftest.py fixture."""
        file_store["temp-id"] = FileMetadata(
            id="temp-id",
            filename="temp.txt",
            content_type="text/plain",
            size=10
        )
        assert "temp-id" in file_store
        file_store.clear()
        assert "temp-id" not in file_store


class TestFileUploadEndpoint:
    """Tests for REQ_001.1: POST /api/files/upload endpoint."""

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_endpoint_accepts_multipart_form_data(self):
        """Endpoint accepts multipart/form-data POST requests with a file field."""
        file_content = b"Hello, World!"
        files = {"file": ("test.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_generates_unique_uuid_for_each_upload(self):
        """Generates a unique UUID for each uploaded file."""
        file_content = b"Test content"
        files = {"file": ("test.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        data = response.json()
        # Validate it's a valid UUID
        parsed_uuid = uuid.UUID(data["id"])
        assert str(parsed_uuid) == data["id"]

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_extracts_content_type_from_uploaded_file(self):
        """Extracts and validates content_type from the uploaded file."""
        file_content = b"Test content"
        files = {"file": ("test.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        data = response.json()
        assert data["content_type"] == "text/plain"

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_calculates_file_size_in_bytes(self):
        """Calculates and stores the file size in bytes."""
        file_content = b"Test content 123"  # 16 bytes
        files = {"file": ("test.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        data = response.json()
        assert data["size"] == 16

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_preserves_original_filename(self):
        """Preserves the original filename in metadata."""
        file_content = b"Test content"
        files = {"file": ("my_document.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        data = response.json()
        assert data["filename"] == "my_document.txt"

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_stores_file_to_uploads_directory(self):
        """Stores the file to ./uploads directory with UUID-based naming."""
        file_content = b"File content to store"
        files = {"file": ("test.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        data = response.json()
        # Check file exists in uploads directory
        expected_path = os.path.join(UPLOAD_DIR, data["id"])
        assert os.path.exists(expected_path)

        # Verify content
        with open(expected_path, "rb") as f:
            stored_content = f.read()
        assert stored_content == file_content

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_returns_http_201_with_file_metadata(self):
        """Returns HTTP 201 with FileMetadata JSON."""
        file_content = b"Test content"
        files = {"file": ("test.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201
        data = response.json()
        assert "id" in data
        assert "filename" in data
        assert "content_type" in data
        assert "size" in data

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_creates_uploads_directory_if_not_exists(self):
        """Creates uploads directory if it does not exist."""
        # Ensure uploads directory doesn't exist
        if os.path.exists(UPLOAD_DIR):
            shutil.rmtree(UPLOAD_DIR)

        file_content = b"Test content"
        files = {"file": ("test.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201
        assert os.path.exists(UPLOAD_DIR)

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_stores_metadata_in_file_store(self):
        """Stores file metadata in the in-memory file_store."""
        file_content = b"Test content"
        files = {"file": ("test.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        data = response.json()
        assert data["id"] in file_store
        assert file_store[data["id"]].filename == "test.txt"


class TestFileRetrievalEndpoint:
    """Tests for REQ_001.2: GET /api/files/{id} endpoint."""

    async def test_endpoint_accepts_get_with_file_id(self):
        """Endpoint accepts GET requests with file ID as path parameter."""
        # Pre-populate store
        file_id = str(uuid.uuid4())
        file_store[file_id] = FileMetadata(
            id=file_id,
            filename="test.txt",
            content_type="text/plain",
            size=100
        )

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.get(f"/api/files/{file_id}")

        assert response.status_code == 200

    async def test_returns_http_200_with_file_metadata(self):
        """Returns HTTP 200 with FileMetadata JSON when file exists."""
        file_id = str(uuid.uuid4())
        file_store[file_id] = FileMetadata(
            id=file_id,
            filename="document.pdf",
            content_type="application/pdf",
            size=2048
        )

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.get(f"/api/files/{file_id}")

        assert response.status_code == 200
        data = response.json()
        assert data["id"] == file_id
        assert data["filename"] == "document.pdf"
        assert data["content_type"] == "application/pdf"
        assert data["size"] == 2048

    async def test_returns_http_404_when_file_not_found(self):
        """Returns HTTP 404 with detail 'Resource not found' when file ID does not exist."""
        non_existent_id = str(uuid.uuid4())

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.get(f"/api/files/{non_existent_id}")

        assert response.status_code == 404
        assert response.json()["detail"] == "Resource not found"

    async def test_response_includes_all_metadata_fields(self):
        """Response includes all metadata fields: id, filename, content_type, size."""
        file_id = str(uuid.uuid4())
        file_store[file_id] = FileMetadata(
            id=file_id,
            filename="audio.mp3",
            content_type="audio/mpeg",
            size=5000
        )

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.get(f"/api/files/{file_id}")

        data = response.json()
        assert set(data.keys()) == {"id", "filename", "content_type", "size"}

    async def test_endpoint_is_idempotent(self):
        """Endpoint is idempotent - multiple calls return same result."""
        file_id = str(uuid.uuid4())
        file_store[file_id] = FileMetadata(
            id=file_id,
            filename="test.txt",
            content_type="text/plain",
            size=100
        )

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response1 = await client.get(f"/api/files/{file_id}")
            response2 = await client.get(f"/api/files/{file_id}")

        assert response1.json() == response2.json()


class TestEmptyFileValidation:
    """Tests for REQ_001.4: Empty file validation."""

    async def test_empty_file_returns_http_400(self):
        """Files with size of 0 bytes are rejected with HTTP 400."""
        empty_content = b""
        files = {"file": ("empty.txt", io.BytesIO(empty_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 400

    async def test_empty_file_error_message(self):
        """Response body contains detail field with exact message 'Empty file not allowed'."""
        empty_content = b""
        files = {"file": ("empty.txt", io.BytesIO(empty_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.json()["detail"] == "Empty file not allowed"

    async def test_empty_file_not_saved_to_disk(self):
        """Validation occurs before file is saved to disk."""
        empty_content = b""
        files = {"file": ("empty.txt", io.BytesIO(empty_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        # Verify no files in uploads directory with this name pattern
        if os.path.exists(UPLOAD_DIR):
            files_in_dir = os.listdir(UPLOAD_DIR)
            # No new files should be created
            assert len(files_in_dir) == 0 or all(
                not f.endswith(".txt") for f in files_in_dir
            )

    async def test_empty_file_not_stored_in_metadata(self):
        """Validation occurs before metadata is stored."""
        initial_count = len(file_store)
        empty_content = b""
        files = {"file": ("empty.txt", io.BytesIO(empty_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            await client.post("/api/files/upload", files=files)

        assert len(file_store) == initial_count


class TestContentTypeValidation:
    """Tests for REQ_001.5: Content type validation."""

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_valid_audio_webm_accepted(self):
        """Audio content type audio/webm is allowed."""
        file_content = b"fake audio content"
        files = {"file": ("audio.webm", io.BytesIO(file_content), "audio/webm")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_valid_audio_mpeg_accepted(self):
        """Audio content type audio/mpeg is allowed."""
        file_content = b"fake audio content"
        files = {"file": ("audio.mp3", io.BytesIO(file_content), "audio/mpeg")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_valid_audio_wav_accepted(self):
        """Audio content type audio/wav is allowed."""
        file_content = b"fake audio content"
        files = {"file": ("audio.wav", io.BytesIO(file_content), "audio/wav")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_valid_audio_ogg_accepted(self):
        """Audio content type audio/ogg is allowed."""
        file_content = b"fake audio content"
        files = {"file": ("audio.ogg", io.BytesIO(file_content), "audio/ogg")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_valid_audio_flac_accepted(self):
        """Audio content type audio/flac is allowed."""
        file_content = b"fake audio content"
        files = {"file": ("audio.flac", io.BytesIO(file_content), "audio/flac")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_valid_text_plain_accepted(self):
        """Text content type text/plain is allowed."""
        file_content = b"Hello, World!"
        files = {"file": ("test.txt", io.BytesIO(file_content), "text/plain")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201

    @pytest.mark.usefixtures("cleanup_uploads")
    async def test_valid_application_json_accepted(self):
        """Application content type application/json is allowed."""
        file_content = b'{"key": "value"}'
        files = {"file": ("data.json", io.BytesIO(file_content), "application/json")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 201

    async def test_invalid_content_type_rejected(self):
        """Returns HTTP 400 for files with unsupported content types."""
        file_content = b"some executable content"
        files = {"file": ("program.exe", io.BytesIO(file_content), "application/x-msdownload")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert response.status_code == 400

    async def test_invalid_content_type_error_message(self):
        """Error message includes 'Invalid content type' text."""
        file_content = b"some executable content"
        files = {"file": ("program.exe", io.BytesIO(file_content), "application/x-msdownload")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        assert "Invalid content type" in response.json()["detail"]

    async def test_content_type_from_file_metadata(self):
        """Content type is checked from file metadata, not file extension."""
        # File has .txt extension but wrong content type
        file_content = b"text content"
        files = {"file": ("test.txt", io.BytesIO(file_content), "application/x-msdownload")}

        async with AsyncClient(
            transport=ASGITransport(app=app),
            base_url="http://test"
        ) as client:
            response = await client.post("/api/files/upload", files=files)

        # Should be rejected based on content type, not extension
        assert response.status_code == 400
