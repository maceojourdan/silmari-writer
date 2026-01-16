'use client';

import { useEffect } from 'react';
import { Copy, RefreshCw, Send, Edit } from 'lucide-react';
import { useConversationStore } from '@/lib/store';

interface ButtonRibbonProps {
  messageId: string;
  content: string;
}

interface LoadingSpinnerProps {
  size?: 'sm' | 'md' | 'lg';
  className?: string;
}

const LoadingSpinner = ({ size = 'sm', className }: LoadingSpinnerProps) => {
  const sizeClasses = {
    sm: 'w-4 h-4',
    md: 'w-6 h-6',
    lg: 'w-8 h-8',
  };

  return (
    <div
      className={`${sizeClasses[size]} border-2 border-current border-t-transparent rounded-full animate-spin ${className || ''}`}
      data-testid="loading-spinner"
    />
  );
};

export default function ButtonRibbon({ messageId, content }: ButtonRibbonProps) {
  const {
    buttonStates,
    isMessageBlocked,
    setNonBlockingOperation,
    clearNonBlockingOperation,
  } = useConversationStore();

  const buttonState = buttonStates[messageId];
  const isBlocked = isMessageBlocked(messageId);
  const blockingOperation = buttonState?.blockingOperation;
  const copyState = buttonState?.copy;

  // Auto-clear copy state after 2 seconds
  // Note: clearNonBlockingOperation is stable (from Zustand), safe to depend on
  useEffect(() => {
    if (copyState?.isActive) {
      const timer = setTimeout(() => {
        clearNonBlockingOperation(messageId, 'copy');
      }, 2000);

      return () => clearTimeout(timer); // Cleanup on unmount
    }
  }, [copyState?.isActive, messageId, clearNonBlockingOperation]);

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(content);
      setNonBlockingOperation(messageId, 'copy');
    } catch (error) {
      console.error('Failed to copy to clipboard:', error);
    }
  };

  const buttonBaseClasses = "flex items-center gap-1 px-3 py-1.5 text-sm rounded-md bg-secondary text-secondary-foreground hover:bg-secondary/80 transition-colors disabled:opacity-50 disabled:cursor-not-allowed";

  return (
    <div className="mt-2 flex items-center gap-2">
      {/* Copy button (non-blocking) */}
      <button
        className={buttonBaseClasses}
        onClick={handleCopy}
        aria-label="Copy message"
      >
        <Copy className="w-4 h-4" />
        {copyState?.isActive ? 'Copied!' : 'Copy'}
      </button>

      {/* Regenerate button (blocking) */}
      <button
        className={buttonBaseClasses}
        disabled={isBlocked}
        aria-label="Regenerate message"
      >
        {blockingOperation?.type === 'regenerate' && blockingOperation.isLoading ? (
          <LoadingSpinner />
        ) : (
          <RefreshCw className="w-4 h-4" />
        )}
        Regenerate
      </button>

      {/* Send to API button (blocking) */}
      <button
        className={buttonBaseClasses}
        disabled={isBlocked}
        aria-label="Send to API"
      >
        {blockingOperation?.type === 'sendToAPI' && blockingOperation.isLoading ? (
          <LoadingSpinner />
        ) : (
          <Send className="w-4 h-4" />
        )}
        Send to API
      </button>

      {/* Edit button (blocking) */}
      <button
        className={buttonBaseClasses}
        disabled={isBlocked}
        aria-label="Edit message"
      >
        {blockingOperation?.type === 'edit' && blockingOperation.isLoading ? (
          <LoadingSpinner />
        ) : (
          <Edit className="w-4 h-4" />
        )}
        Edit
      </button>

      {/* Error message display */}
      {blockingOperation?.error && (
        <div className="text-sm text-red-600 ml-2">
          {blockingOperation.error}
        </div>
      )}
    </div>
  );
}
