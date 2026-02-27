import { defineConfig } from 'vitest/config'
import react from '@vitejs/plugin-react'
import path from 'path'

export default defineConfig({
  plugins: [react()],
  test: {
    environment: 'jsdom',
    setupFiles: ['./test/setup.ts'],
    globals: true,
    include: ['**/__tests__/**/*.{test,spec}.{ts,tsx}', '**/*.{test,spec}.{ts,tsx}'],
    exclude: ['node_modules', 'e2e/**/*'],
  },
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
      // Stub missing optional deps used by components but not installed in test env
      'sonner': path.resolve(__dirname, './test/__mocks__/sonner.ts'),
    },
  },
})
