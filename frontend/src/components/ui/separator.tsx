import * as React from 'react';
import { cn } from '@/lib/cn';

interface SeparatorProps extends React.HTMLAttributes<HTMLDivElement> {
  orientation?: 'horizontal' | 'vertical';
  decorative?: boolean;
}

const Separator = React.forwardRef<HTMLDivElement, SeparatorProps>(
  ({ className, orientation = 'horizontal', decorative = true, ...props }, ref) => {
    return (
      <div
        ref={ref}
        data-slot="separator-root"
        role={decorative ? undefined : 'separator'}
        aria-orientation={orientation}
        className={cn(
          'shrink-0 bg-border/60',
          orientation === 'horizontal' ? 'h-0.5 w-full' : 'h-full w-0.5',
          className,
        )}
        {...props}
      />
    );
  },
);
Separator.displayName = 'Separator';

export { Separator };
