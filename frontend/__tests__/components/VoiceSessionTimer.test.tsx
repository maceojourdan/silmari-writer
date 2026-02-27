import { describe, it, expect } from 'vitest';
import { render, screen } from '@testing-library/react';

describe('VoiceSessionTimer', () => {
  it('should not render when timeRemaining is null', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    const { container } = render(<VoiceSessionTimer timeRemaining={null} />);
    expect(container.firstChild).toBeNull();
  });

  it('should display time in MM:SS format', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    render(<VoiceSessionTimer timeRemaining={1234} />);
    expect(screen.getByText('20:34')).toBeInTheDocument();
  });

  it('should show normal color when time > 5 minutes', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    render(<VoiceSessionTimer timeRemaining={600} />);
    const timer = screen.getByTestId('voice-session-timer');
    expect(timer.className).toContain('text-muted-foreground');
  });

  it('should show warning color when time <= 5 minutes', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    render(<VoiceSessionTimer timeRemaining={299} />);
    const timer = screen.getByTestId('voice-session-timer');
    expect(timer.className).toContain('text-yellow');
  });

  it('should show critical color when time <= 1 minute', async () => {
    const { default: VoiceSessionTimer } = await import(
      '@/components/chat/VoiceSessionTimer'
    );
    render(<VoiceSessionTimer timeRemaining={59} />);
    const timer = screen.getByTestId('voice-session-timer');
    expect(timer.className).toContain('text-red');
  });
});
