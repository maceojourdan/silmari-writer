'use client';

import { useState, useEffect } from 'react';
import { X } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Textarea } from '@/components/ui/textarea';

interface EditMessageModalProps {
  isOpen: boolean;
  content: string;
  onSave: (newContent: string) => void;
  onCancel: () => void;
}

export default function EditMessageModal({
  isOpen,
  content,
  onSave,
  onCancel,
}: EditMessageModalProps) {
  const [editedContent, setEditedContent] = useState(content);

  useEffect(() => {
    setEditedContent(content);
  }, [content]);

  useEffect(() => {
    const handleEscape = (e: KeyboardEvent) => {
      if (e.key === 'Escape') {
        onCancel();
      }
    };

    if (isOpen) {
      document.addEventListener('keydown', handleEscape);
      return () => document.removeEventListener('keydown', handleEscape);
    }
  }, [isOpen, onCancel]);

  if (!isOpen) return null;

  const handleSave = () => {
    onSave(editedContent);
  };

  return (
    <div
      className="fixed inset-0 z-50 flex items-center justify-center bg-black/50"
      role="dialog"
      aria-modal="true"
    >
      <div className="mx-4 w-full max-w-2xl rounded-lg border border-border bg-card p-6 shadow-xl">
        <div className="flex justify-between items-center mb-4">
          <h2 className="text-xl font-bold font-serif">Edit Message</h2>
          <button
            onClick={onCancel}
            className="rounded p-1 hover:bg-accent"
            aria-label="Close modal"
          >
            <X className="w-5 h-5" />
          </button>
        </div>

        <Textarea
          className="h-64 resize-none"
          value={editedContent}
          onChange={(e) => setEditedContent(e.target.value)}
          autoFocus
        />

        <div className="mt-2 text-sm text-muted-foreground">
          {editedContent.length} characters
        </div>

        <div className="flex justify-end gap-2 mt-4">
          <Button
            onClick={onCancel}
            variant="outline"
          >
            Cancel
          </Button>
          <Button
            onClick={handleSave}
            disabled={editedContent.trim().length === 0}
          >
            Save
          </Button>
        </div>
      </div>
    </div>
  );
}
