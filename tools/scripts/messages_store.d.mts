export function readMessages(file: string): unknown[];
export function updateMessages<T>(file: string, change: (all: any[]) => T): T;
export function nextMessageId(file: string, all: unknown[], more?: string[]): string;
export function clearMessages(file: string, force?: boolean): { cleared: number; pending: number };
export function archiveOf(file: string): string;
