type SendEventFn = (event: Record<string, unknown>) => void;

export class TTSQueue {
  private queue: string[] = [];
  private isProcessing = false;
  private sendEvent: SendEventFn;

  constructor(sendEvent: SendEventFn) {
    this.sendEvent = sendEvent;
  }

  setSendEvent(sendEvent: SendEventFn): void {
    this.sendEvent = sendEvent;
  }

  enqueue(text: string): void {
    if (!text.trim()) return;

    if (!this.isProcessing) {
      this.isProcessing = true;
      this.playText(text);
    } else {
      this.queue.push(text);
    }
  }

  handleResponseDone(): void {
    if (this.queue.length > 0) {
      const next = this.queue.shift()!;
      this.playText(next);
    } else {
      this.isProcessing = false;
    }
  }

  reset(): void {
    this.queue = [];
  }

  get length(): number {
    return this.queue.length;
  }

  private playText(text: string): void {
    this.sendEvent({
      type: 'conversation.item.create',
      item: {
        type: 'message',
        role: 'user',
        content: [{ type: 'input_text', text }],
      },
    });
    this.sendEvent({
      type: 'response.create',
      response: {
        modalities: ['audio'],
      },
    });
  }
}
