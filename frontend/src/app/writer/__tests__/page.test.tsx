import { render, screen } from '@testing-library/react';
import { describe, expect, it, vi } from 'vitest';
import WriterPage from '../page';

vi.mock('@/modules/session/StartSessionRouteAdapter', () => ({
  StartSessionRouteAdapter: () => <div data-testid="start-session-route-adapter" />,
}));

describe('Writer entry route', () => {
  it('renders workflow entry UI in production route', () => {
    render(<WriterPage />);
    expect(screen.getByTestId('workflow-entry')).toBeInTheDocument();
    expect(screen.getByTestId('start-session-route-adapter')).toBeInTheDocument();
  });
});

