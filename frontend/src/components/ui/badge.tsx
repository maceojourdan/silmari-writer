import * as React from 'react';
import { cn } from '@/lib/cn';

const badgeVariants = {
  default: 'border-transparent bg-primary text-primary-foreground [a&]:hover:bg-primary/90',
  secondary: 'border-transparent bg-secondary text-secondary-foreground [a&]:hover:bg-secondary/90',
  outline: 'text-foreground [a&]:hover:bg-accent [a&]:hover:text-accent-foreground',
  destructive:
    'border-transparent bg-destructive text-white [a&]:hover:bg-destructive/90',
} as const;

type BadgeVariant = keyof typeof badgeVariants;

interface BadgeProps extends React.HTMLAttributes<HTMLDivElement> {
  variant?: BadgeVariant;
}

function Badge({ className, variant = 'default', ...props }: BadgeProps) {
  return (
    <div
      className={cn(
        'inline-flex items-center justify-center rounded-md border px-2 py-0.5 text-xs font-medium',
        'w-fit whitespace-nowrap shrink-0 [&>svg]:size-3 gap-1 [&>svg]:pointer-events-none',
        'focus-visible:border-ring focus-visible:ring-ring/50 focus-visible:ring-[3px]',
        'aria-invalid:ring-destructive/20 dark:aria-invalid:ring-destructive/40 aria-invalid:border-destructive',
        'transition-[color,box-shadow] overflow-hidden',
        badgeVariants[variant],
        className,
      )}
      {...props}
    />
  );
}

export { Badge };
