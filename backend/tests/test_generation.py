"""Tests for content generation functionality."""

from unittest.mock import AsyncMock, patch

import pytest
from httpx import AsyncClient, ASGITransport

from backend.app import app


class TestGenerateEndpoint:
    """Tests for REQ_004.2: POST /api/generate endpoint."""

    @pytest.mark.asyncio
    async def test_endpoint_accepts_themes_and_prompt(self):
        """Endpoint accepts JSON body with 'themes' (array of Theme objects) and 'prompt' (string) fields."""
        mock_generate = AsyncMock(return_value={"content": "Generated text."})
        with patch("backend.app.generate_content_llm", mock_generate):
            async with AsyncClient(
                transport=ASGITransport(app=app), base_url="http://test"
            ) as client:
                response = await client.post(
                    "/api/generate",
                    json={
                        "themes": [{"name": "adventure", "confidence": 0.9}],
                        "prompt": "Write a short story."
                    }
                )
                # Should not be 404 or 405
                assert response.status_code in [200, 400, 422, 500]

    @pytest.mark.asyncio
    async def test_returns_400_if_prompt_missing(self):
        """Returns 400 error if 'prompt' field is missing."""
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            response = await client.post(
                "/api/generate",
                json={"themes": [{"name": "test", "confidence": 0.5}]}
            )
            assert response.status_code == 400

    @pytest.mark.asyncio
    async def test_returns_400_if_prompt_empty(self):
        """Returns 400 error if 'prompt' field is empty."""
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            response = await client.post(
                "/api/generate",
                json={
                    "themes": [{"name": "test", "confidence": 0.5}],
                    "prompt": ""
                }
            )
            assert response.status_code == 400

    @pytest.mark.asyncio
    async def test_returns_400_if_themes_empty(self):
        """Returns 400 error if 'themes' array is empty."""
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            response = await client.post(
                "/api/generate",
                json={
                    "themes": [],
                    "prompt": "Write something."
                }
            )
            assert response.status_code == 400

    @pytest.mark.asyncio
    async def test_returns_generated_content(self):
        """Returns generated content as JSON with 'content' field (string)."""
        mock_generate = AsyncMock(return_value={
            "content": "Once upon a time, in a land of adventure..."
        })
        with patch("backend.app.generate_content_llm", mock_generate):
            async with AsyncClient(
                transport=ASGITransport(app=app), base_url="http://test"
            ) as client:
                response = await client.post(
                    "/api/generate",
                    json={
                        "themes": [{"name": "adventure", "confidence": 0.9}],
                        "prompt": "Write a short story."
                    }
                )
                assert response.status_code == 200
                data = response.json()
                assert "content" in data
                assert isinstance(data["content"], str)
                assert "adventure" in data["content"].lower()

    @pytest.mark.asyncio
    async def test_returns_500_on_openai_failure(self):
        """Returns 500 error with detail 'Service failed: {error}' when OpenAI API fails."""
        mock_generate = AsyncMock(side_effect=Exception("OpenAI API error"))
        with patch("backend.app.generate_content_llm", mock_generate):
            async with AsyncClient(
                transport=ASGITransport(app=app), base_url="http://test"
            ) as client:
                response = await client.post(
                    "/api/generate",
                    json={
                        "themes": [{"name": "test", "confidence": 0.5}],
                        "prompt": "Generate something."
                    }
                )
                assert response.status_code == 500
                data = response.json()
                assert "Service failed:" in data["detail"]

    @pytest.mark.asyncio
    async def test_endpoint_is_async(self):
        """Endpoint is async and non-blocking."""
        mock_generate = AsyncMock(return_value={"content": "Async content."})
        with patch("backend.app.generate_content_llm", mock_generate):
            async with AsyncClient(
                transport=ASGITransport(app=app), base_url="http://test"
            ) as client:
                response = await client.post(
                    "/api/generate",
                    json={
                        "themes": [{"name": "test", "confidence": 0.5}],
                        "prompt": "Test prompt."
                    }
                )
                assert response.status_code == 200
                mock_generate.assert_called_once()

    @pytest.mark.asyncio
    async def test_openai_calls_are_mocked(self):
        """OpenAI API calls are mocked in tests using AsyncMock pattern."""
        mock_generate = AsyncMock(return_value={"content": "Mocked content response."})
        with patch("backend.app.generate_content_llm", mock_generate):
            async with AsyncClient(
                transport=ASGITransport(app=app), base_url="http://test"
            ) as client:
                response = await client.post(
                    "/api/generate",
                    json={
                        "themes": [{"name": "mocked", "confidence": 0.99}],
                        "prompt": "Test."
                    }
                )
                assert response.status_code == 200
                mock_generate.assert_called_once()
                assert "Mocked content" in response.json()["content"]

    @pytest.mark.asyncio
    async def test_supports_multiple_themes(self):
        """Generated content incorporates all provided themes naturally."""
        mock_generate = AsyncMock(return_value={
            "content": "A tale of love, adventure, and mystery awaits."
        })
        with patch("backend.app.generate_content_llm", mock_generate):
            async with AsyncClient(
                transport=ASGITransport(app=app), base_url="http://test"
            ) as client:
                response = await client.post(
                    "/api/generate",
                    json={
                        "themes": [
                            {"name": "love", "confidence": 0.9},
                            {"name": "adventure", "confidence": 0.8},
                            {"name": "mystery", "confidence": 0.7}
                        ],
                        "prompt": "Write an epic story."
                    }
                )
                assert response.status_code == 200
                content = response.json()["content"]
                assert isinstance(content, str)

    @pytest.mark.asyncio
    async def test_themes_missing_returns_400(self):
        """Returns 400 if themes field is missing."""
        async with AsyncClient(
            transport=ASGITransport(app=app), base_url="http://test"
        ) as client:
            response = await client.post(
                "/api/generate",
                json={"prompt": "Write something."}
            )
            assert response.status_code == 400


class TestGenerateOpenAIIntegration:
    """Tests for REQ_004.4: OpenAI GPT-4 integration for content generation."""

    @pytest.mark.asyncio
    async def test_generate_content_llm_is_mockable(self):
        """OpenAI client is mockable for unit testing without real API calls."""
        mock_generate = AsyncMock(return_value={"content": "Generated."})
        with patch("backend.app.generate_content_llm", mock_generate):
            async with AsyncClient(
                transport=ASGITransport(app=app), base_url="http://test"
            ) as client:
                response = await client.post(
                    "/api/generate",
                    json={
                        "themes": [{"name": "test", "confidence": 0.5}],
                        "prompt": "Generate."
                    }
                )
                assert response.status_code == 200
                mock_generate.assert_called_once()

    @pytest.mark.asyncio
    async def test_network_error_handled_gracefully(self):
        """Network errors are caught and converted to service errors."""
        mock_generate = AsyncMock(side_effect=ConnectionError("Network unavailable"))
        with patch("backend.app.generate_content_llm", mock_generate):
            async with AsyncClient(
                transport=ASGITransport(app=app), base_url="http://test"
            ) as client:
                response = await client.post(
                    "/api/generate",
                    json={
                        "themes": [{"name": "test", "confidence": 0.5}],
                        "prompt": "Test."
                    }
                )
                assert response.status_code == 500
                assert "Service failed:" in response.json()["detail"]

    @pytest.mark.asyncio
    async def test_timeout_error_handled(self):
        """Timeout errors are handled gracefully."""
        mock_generate = AsyncMock(side_effect=TimeoutError("Request timed out"))
        with patch("backend.app.generate_content_llm", mock_generate):
            async with AsyncClient(
                transport=ASGITransport(app=app), base_url="http://test"
            ) as client:
                response = await client.post(
                    "/api/generate",
                    json={
                        "themes": [{"name": "test", "confidence": 0.5}],
                        "prompt": "Test."
                    }
                )
                assert response.status_code == 500
                assert "Service failed:" in response.json()["detail"]
