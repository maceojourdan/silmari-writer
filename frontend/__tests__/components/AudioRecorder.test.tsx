import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { render, screen, fireEvent, waitFor, act } from '@testing-library/react'
import AudioRecorder, { MAX_RECORDING_TIME_SECONDS } from '@/components/chat/AudioRecorder'
import { toast } from 'sonner'

// Mock sonner toast
vi.mock('sonner', () => ({
  toast: {
    info: vi.fn(),
    error: vi.fn(),
    success: vi.fn(),
  },
}))

// Mock MediaRecorder
class MockMediaRecorder {
  static isTypeSupported = vi.fn().mockReturnValue(true)

  state: 'inactive' | 'recording' | 'paused' = 'inactive'
  ondataavailable: ((e: { data: Blob }) => void) | null = null
  onstop: (() => void) | null = null
  onerror: ((e: Event) => void) | null = null
  stream: MediaStream
  options?: MediaRecorderOptions

  constructor(stream: MediaStream, options?: MediaRecorderOptions) {
    this.stream = stream
    this.options = options
  }

  start() {
    this.state = 'recording'
  }

  stop() {
    this.state = 'inactive'
    // Simulate data being available
    const blob = new Blob(['mock audio data'], { type: this.options?.mimeType || 'audio/webm' })
    if (this.ondataavailable) {
      this.ondataavailable({ data: blob })
    }
    if (this.onstop) {
      this.onstop()
    }
  }
}

// Mock MediaStream
class MockMediaStream {
  getTracks() {
    return [{ stop: vi.fn() }]
  }
}

// Mock navigator.mediaDevices
const mockGetUserMedia = vi.fn()

// Mock URL.createObjectURL and revokeObjectURL
const mockCreateObjectURL = vi.fn().mockReturnValue('blob:mock-url')
const mockRevokeObjectURL = vi.fn()

beforeEach(() => {
  // Reset mocks
  vi.clearAllMocks()

  // Setup MediaRecorder mock
  vi.stubGlobal('MediaRecorder', MockMediaRecorder)

  // Setup navigator.mediaDevices mock
  Object.defineProperty(global.navigator, 'mediaDevices', {
    value: { getUserMedia: mockGetUserMedia },
    writable: true,
    configurable: true,
  })

  // Setup URL mock
  vi.stubGlobal('URL', {
    ...URL,
    createObjectURL: mockCreateObjectURL,
    revokeObjectURL: mockRevokeObjectURL,
  })

  // Default: permission granted
  mockGetUserMedia.mockResolvedValue(new MockMediaStream())
})

afterEach(() => {
  vi.unstubAllGlobals()
  vi.useRealTimers()
})

describe('AudioRecorder', () => {
  describe('initial state', () => {
    it('should render record button', () => {
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      expect(screen.getByRole('button', { name: /record/i })).toBeInTheDocument()
    })

    it('should not show timer initially', () => {
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      expect(screen.queryByText(/\d{2}:\d{2}/)).not.toBeInTheDocument()
    })

    it('should not show playback controls initially', () => {
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      expect(screen.queryByRole('button', { name: /play/i })).not.toBeInTheDocument()
      expect(screen.queryByRole('button', { name: /re-record/i })).not.toBeInTheDocument()
    })
  })

  describe('microphone permission', () => {
    it('should request microphone permission when record is clicked', async () => {
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      fireEvent.click(screen.getByRole('button', { name: /record/i }))

      await waitFor(() => {
        expect(mockGetUserMedia).toHaveBeenCalledWith({ audio: true })
      })
    })

    it('should show error when permission is denied', async () => {
      mockGetUserMedia.mockRejectedValueOnce(new Error('Permission denied'))

      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      fireEvent.click(screen.getByRole('button', { name: /record/i }))

      await waitFor(() => {
        expect(screen.getByText(/microphone access/i)).toBeInTheDocument()
      })
    })
  })

  describe('recording state', () => {
    it('should show stop button when recording', async () => {
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      fireEvent.click(screen.getByRole('button', { name: /record/i }))

      await waitFor(() => {
        expect(screen.getByRole('button', { name: /stop/i })).toBeInTheDocument()
      })
    })

    it('should show countdown timer when recording (displays remaining time)', async () => {
      vi.useFakeTimers()
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0) // Flush promises
      })

      // Countdown starts at 05:00 (5 minutes remaining)
      expect(screen.getByText('05:00')).toBeInTheDocument()

      // Advance timer by 5 seconds - should show 04:55 remaining
      await act(async () => {
        await vi.advanceTimersByTimeAsync(5000)
      })

      expect(screen.getByText('04:55')).toBeInTheDocument()
    })

    it('should show recording indicator', async () => {
      vi.useFakeTimers()
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0) // Flush promises
      })

      expect(screen.getByTestId('recording-indicator')).toBeInTheDocument()
    })
  })

  describe('stop recording', () => {
    it('should call onRecordingComplete with audio blob when stop is clicked', async () => {
      vi.useFakeTimers()
      const onRecordingComplete = vi.fn()
      render(<AudioRecorder onRecordingComplete={onRecordingComplete} />)

      // Start recording
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      expect(screen.getByRole('button', { name: /stop/i })).toBeInTheDocument()

      // Stop recording
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /stop/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      expect(onRecordingComplete).toHaveBeenCalledWith(expect.any(Blob))
    })

    it('should show playback controls after stopping', async () => {
      vi.useFakeTimers()
      const onRecordingComplete = vi.fn()
      render(<AudioRecorder onRecordingComplete={onRecordingComplete} />)

      // Start recording
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Stop recording
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /stop/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      expect(screen.getByRole('button', { name: /play/i })).toBeInTheDocument()
      expect(screen.getByRole('button', { name: /re-record/i })).toBeInTheDocument()
    })
  })

  describe('5-minute limit', () => {
    it('should auto-stop recording at 5 minutes', async () => {
      vi.useFakeTimers()
      const onRecordingComplete = vi.fn()
      render(<AudioRecorder onRecordingComplete={onRecordingComplete} />)

      // Start recording
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      expect(screen.getByRole('button', { name: /stop/i })).toBeInTheDocument()

      // Advance timer to 5 minutes
      await act(async () => {
        await vi.advanceTimersByTimeAsync(5 * 60 * 1000)
      })

      expect(onRecordingComplete).toHaveBeenCalled()
    })

    it('should show toast notification when auto-stopped', async () => {
      vi.useFakeTimers()
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      // Start recording
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Advance timer to 5 minutes
      await act(async () => {
        await vi.advanceTimersByTimeAsync(5 * 60 * 1000)
      })

      expect(toast.info).toHaveBeenCalledWith('Recording stopped - maximum 5 minute limit reached')
    })
  })

  describe('countdown timer', () => {
    it('should display countdown timer showing remaining time (not elapsed)', async () => {
      vi.useFakeTimers()
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      // Start recording
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Initially should show 05:00 (5 minutes remaining)
      const timer = screen.getByTestId('countdown-timer')
      expect(timer).toHaveTextContent('05:00')

      // After 10 seconds, should show 04:50
      await act(async () => {
        await vi.advanceTimersByTimeAsync(10000)
      })

      expect(timer).toHaveTextContent('04:50')
    })

    it('should show 00:01 just before auto-stop', async () => {
      vi.useFakeTimers()
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      // Start recording
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Advance to 4:59 elapsed (1 second remaining)
      await act(async () => {
        await vi.advanceTimersByTimeAsync(299 * 1000)
      })

      const timer = screen.getByTestId('countdown-timer')
      expect(timer).toHaveTextContent('00:01')
    })

    it('should have normal color at start of recording', async () => {
      vi.useFakeTimers()
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      const timer = screen.getByTestId('countdown-timer')
      expect(timer).toHaveClass('text-gray-600')
    })

    it('should change to warning color (yellow) at 1 minute remaining', async () => {
      vi.useFakeTimers()
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Advance to 4 minutes elapsed (1 minute remaining)
      await act(async () => {
        await vi.advanceTimersByTimeAsync(4 * 60 * 1000)
      })

      const timer = screen.getByTestId('countdown-timer')
      expect(timer).toHaveClass('text-yellow-500')
    })

    it('should change to critical color (red) at 30 seconds remaining', async () => {
      vi.useFakeTimers()
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Advance to 4:30 elapsed (30 seconds remaining)
      await act(async () => {
        await vi.advanceTimersByTimeAsync((MAX_RECORDING_TIME_SECONDS - 30) * 1000)
      })

      const timer = screen.getByTestId('countdown-timer')
      expect(timer).toHaveClass('text-red-500')
    })
  })

  describe('playback', () => {
    it('should allow playback preview after recording', async () => {
      vi.useFakeTimers()
      const onRecordingComplete = vi.fn()
      render(<AudioRecorder onRecordingComplete={onRecordingComplete} />)

      // Record
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Stop
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /stop/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Play button should be present
      const playButton = screen.getByRole('button', { name: /play/i })
      expect(playButton).toBeInTheDocument()
    })
  })

  describe('re-record', () => {
    it('should clear previous recording and restart when re-record is clicked', async () => {
      vi.useFakeTimers()
      const onRecordingComplete = vi.fn()
      render(<AudioRecorder onRecordingComplete={onRecordingComplete} />)

      // First recording
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /stop/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      expect(screen.getByRole('button', { name: /re-record/i })).toBeInTheDocument()

      // Re-record
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /re-record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Should have reset to recording state
      expect(screen.getByRole('button', { name: /stop/i })).toBeInTheDocument()
      expect(screen.queryByRole('button', { name: /play/i })).not.toBeInTheDocument()
    })

    it('should reset timer when re-recording', async () => {
      vi.useFakeTimers()
      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      // First recording - countdown starts at 05:00
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      expect(screen.getByText('05:00')).toBeInTheDocument()

      // Advance timer - after 10 seconds, should show 04:50 remaining
      await act(async () => {
        await vi.advanceTimersByTimeAsync(10000)
      })
      expect(screen.getByText('04:50')).toBeInTheDocument()

      // Stop
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /stop/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      // Re-record - countdown should reset back to 05:00
      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /re-record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      expect(screen.getByText('05:00')).toBeInTheDocument()
    })
  })

  describe('MediaRecorder type support', () => {
    it('should use webm format when supported', async () => {
      vi.useFakeTimers()
      MockMediaRecorder.isTypeSupported.mockImplementation((type: string) => type === 'audio/webm')

      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      expect(MockMediaRecorder.isTypeSupported).toHaveBeenCalledWith('audio/webm')
    })

    it('should fallback to mp4 when webm is not supported', async () => {
      vi.useFakeTimers()
      MockMediaRecorder.isTypeSupported.mockImplementation((type: string) => type === 'audio/mp4')

      render(<AudioRecorder onRecordingComplete={vi.fn()} />)

      await act(async () => {
        fireEvent.click(screen.getByRole('button', { name: /record/i }))
        await vi.advanceTimersByTimeAsync(0)
      })

      expect(MockMediaRecorder.isTypeSupported).toHaveBeenCalled()
    })
  })
})
