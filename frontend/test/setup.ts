import '@testing-library/jest-dom'

// Node in this environment exposes an empty `localStorage` object (no methods),
// which breaks Zustand persist tests that call storage.setItem/getItem.
// Ensure global localStorage points to jsdom's Storage implementation.
if (typeof window !== 'undefined' && window.localStorage) {
  const candidate = globalThis.localStorage as unknown as { setItem?: unknown } | undefined
  if (!candidate || typeof candidate.setItem !== 'function') {
    Object.defineProperty(globalThis, 'localStorage', {
      value: window.localStorage,
      configurable: true,
      writable: true,
    })
  }
}
