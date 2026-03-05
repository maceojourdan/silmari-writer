import * as React from 'react';
import { cn } from '@/lib/cn';

const ScrollArea = React.forwardRef<HTMLDivElement, React.HTMLAttributes<HTMLDivElement>>(
  ({ className, ...props }, ref) => (
    <div
      ref={ref}
      data-slot="scroll-area"
      className={cn(
        'relative overflow-auto focus-visible:ring-ring/50 transition-[color,box-shadow] outline-none focus-visible:ring-[3px] focus-visible:outline-1',
        className,
      )}
      {...props}
    />
  ),
);
ScrollArea.displayName = 'ScrollArea';

export { ScrollArea };
