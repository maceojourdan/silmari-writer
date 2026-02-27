import { create } from 'zustand'
import { createJSONStorage, persist } from 'zustand/middleware'
import { Message, Project, MessageButtonState, NonBlockingOperationType, BlockingOperationType } from './types'
import type { VoiceSessionState, EditHistory, EditEntry } from './voice-types'
import { createEditEntry, createEditHistory } from './voice-types'

type PersistStorageLike = {
  getItem: (name: string) => string | null
  setItem: (name: string, value: string) => void
  removeItem: (name: string) => void
}

function createMemoryStorage(): PersistStorageLike {
  const memory = new Map<string, string>()
  return {
    getItem: (name) => memory.get(name) ?? null,
    setItem: (name, value) => {
      memory.set(name, value)
    },
    removeItem: (name) => {
      memory.delete(name)
    },
  }
}

function getPersistStorage(): PersistStorageLike {
  const browserStorage =
    typeof window !== 'undefined' ? (window.localStorage as Partial<Storage> | undefined) : undefined
  if (
    browserStorage &&
    typeof browserStorage.getItem === 'function' &&
    typeof browserStorage.setItem === 'function' &&
    typeof browserStorage.removeItem === 'function'
  ) {
    return browserStorage as PersistStorageLike
  }

  const globalStorage = (globalThis as { localStorage?: Partial<Storage> }).localStorage
  if (
    globalStorage &&
    typeof globalStorage.getItem === 'function' &&
    typeof globalStorage.setItem === 'function' &&
    typeof globalStorage.removeItem === 'function'
  ) {
    return globalStorage as PersistStorageLike
  }

  return createMemoryStorage()
}

function toValidDate(value: unknown): Date {
  if (value instanceof Date) {
    return Number.isNaN(value.getTime()) ? new Date() : value
  }

  if (typeof value === 'string' || typeof value === 'number') {
    const parsed = new Date(value)
    return Number.isNaN(parsed.getTime()) ? new Date() : parsed
  }

  return new Date()
}

function normalizeProjects(projects: Project[] | unknown): Project[] {
  if (!Array.isArray(projects)) {
    return []
  }

  return projects.map((project) => ({
    ...project,
    createdAt: toValidDate((project as Project).createdAt),
    updatedAt: toValidDate((project as Project).updatedAt),
  }))
}

function normalizeMessages(messages: Record<string, Message[]> | unknown): Record<string, Message[]> {
  if (!messages || typeof messages !== 'object') {
    return {}
  }

  const normalizedEntries = Object.entries(messages).map(([projectId, projectMessages]) => [
    projectId,
    Array.isArray(projectMessages)
      ? projectMessages.map((message) => ({
          ...message,
          timestamp: toValidDate((message as Message).timestamp),
        }))
      : [],
  ])

  return Object.fromEntries(normalizedEntries)
}

interface ConversationState {
  projects: Project[]
  activeProjectId: string | null
  messages: Record<string, Message[]> // projectId -> messages
  buttonStates: Record<string, MessageButtonState> // messageId -> button state
  _hasHydrated: boolean

  // Hydration
  setHasHydrated: (state: boolean) => void

  // Project actions
  createProject: (name: string) => string
  deleteProject: (id: string) => void
  updateProject: (id: string, updates: Partial<Omit<Project, 'id'>>) => void
  setActiveProject: (id: string) => void

  // Message actions
  addMessage: (projectId: string, message: Omit<Message, 'id'>) => void
  replaceMessage: (projectId: string, oldMessageId: string, newMessage: Message) => void
  getMessages: (projectId: string) => Message[]
  clearMessages: (projectId: string) => void

  // Button state actions (synchronous - updates are immediate)
  setNonBlockingOperation: (messageId: string, operation: NonBlockingOperationType) => void
  clearNonBlockingOperation: (messageId: string, operation: NonBlockingOperationType) => void
  startBlockingOperation: (messageId: string, type: BlockingOperationType) => void
  completeBlockingOperation: (messageId: string) => void
  failBlockingOperation: (messageId: string, error: string) => void
  isMessageBlocked: (messageId: string) => boolean

  // Selectors
  getActiveProject: () => Project | undefined
  getActiveMessages: () => Message[]
  hasMessages: (projectId: string) => boolean
  projectCount: () => number

  // Voice state (session-scoped, not persisted)
  readAloudEnabled: boolean
  voiceSessionState: VoiceSessionState
  editHistory: EditHistory | null

  // Voice actions
  setReadAloud: (enabled: boolean) => void
  setVoiceSessionState: (state: VoiceSessionState) => void
  initEditHistory: (projectId: string, sessionId: string) => void
  snapshotOriginal: (messageId: string, content: string) => void
  pushEdit: (params: Omit<EditEntry, 'timestamp'>) => void
  popEdit: () => { messageId: string; previousContent: string } | null
  clearEditHistory: () => void
}

export const useConversationStore = create<ConversationState>()(
  persist(
    (set, get) => ({
      projects: [],
      activeProjectId: null,
      messages: {},
      buttonStates: {},
      _hasHydrated: false,

      setHasHydrated: (state) => {
        set({ _hasHydrated: state })
      },

      createProject: (name) => {
        const id = crypto.randomUUID()
        const project: Project = {
          id,
          name,
          createdAt: new Date(),
          updatedAt: new Date(),
        }
        set((state) => ({
          projects: [...state.projects, project],
          activeProjectId: id,
        }))
        return id
      },

      deleteProject: (id) => {
        set((state) => {
          // eslint-disable-next-line @typescript-eslint/no-unused-vars
          const { [id]: _deleted, ...remainingMessages } = state.messages
          const remainingProjects = state.projects.filter((p) => p.id !== id)
          return {
            projects: remainingProjects,
            messages: remainingMessages,
            activeProjectId:
              state.activeProjectId === id
                ? remainingProjects[0]?.id ?? null
                : state.activeProjectId,
          }
        })
      },

      updateProject: (id, updates) => {
        set((state) => ({
          projects: state.projects.map((p) =>
            p.id === id ? { ...p, ...updates, updatedAt: new Date() } : p
          ),
        }))
      },

      setActiveProject: (id) => {
        set({ activeProjectId: id })
      },

      addMessage: (projectId, message) => {
        const fullMessage: Message = {
          ...message,
          id: crypto.randomUUID(),
          timestamp: toValidDate(message.timestamp),
        }
        set((state) => ({
          messages: {
            ...state.messages,
            [projectId]: [...(state.messages[projectId] || []), fullMessage],
          },
        }))
      },

      replaceMessage: (projectId, oldMessageId, newMessage) => {
        set((state) => {
          const projectMessages = state.messages[projectId] || []
          const index = projectMessages.findIndex(m => m.id === oldMessageId)
          if (index === -1) return state

          const updatedMessages = [...projectMessages]
          updatedMessages[index] = {
            ...newMessage,
            timestamp: toValidDate(newMessage.timestamp),
          }

          return {
            messages: {
              ...state.messages,
              [projectId]: updatedMessages,
            },
          }
        })
      },

      getMessages: (projectId) => {
        return get().messages[projectId] || []
      },

      clearMessages: (projectId) => {
        set((state) => ({
          messages: {
            ...state.messages,
            [projectId]: [],
          },
        }))
      },

      // Selectors
      getActiveProject: () => {
        const state = get()
        return state.projects.find((p) => p.id === state.activeProjectId)
      },

      getActiveMessages: () => {
        const state = get()
        if (!state.activeProjectId) return []
        return state.messages[state.activeProjectId] || []
      },

      hasMessages: (projectId) => {
        const messages = get().messages[projectId]
        return messages !== undefined && messages.length > 0
      },

      projectCount: () => {
        return get().projects.length
      },

      // Button state actions
      setNonBlockingOperation: (messageId, operation) => {
        set((state) => ({
          buttonStates: {
            ...state.buttonStates,
            [messageId]: {
              ...state.buttonStates[messageId],
              [operation]: {
                isActive: true,
                timestamp: Date.now(),
              },
            },
          },
        }))
      },

      // Note: Components are responsible for calling clearNonBlockingOperation
      // after timeout (typically 2 seconds). Store does not auto-clear copy states.
      clearNonBlockingOperation: (messageId, operation) => {
        set((state) => {
          const messageState = state.buttonStates[messageId]
          if (!messageState) return state

          const updatedMessageState = {
            ...messageState,
            [operation]: undefined,
          }

          // Clean up if no state remains
          const hasAnyState = updatedMessageState.copy || updatedMessageState.blockingOperation
          if (!hasAnyState) {
            const { [messageId]: _removed, ...remainingStates } = state.buttonStates
            return { buttonStates: remainingStates }
          }

          return {
            buttonStates: {
              ...state.buttonStates,
              [messageId]: updatedMessageState,
            },
          }
        })
      },
      startBlockingOperation: (messageId, type) => {
        set((state) => ({
          buttonStates: {
            ...state.buttonStates,
            [messageId]: {
              ...state.buttonStates[messageId],
              blockingOperation: {
                type,
                isLoading: true,
              },
            },
          },
        }))
      },
      completeBlockingOperation: (messageId) => {
        set((state) => {
          const messageState = state.buttonStates[messageId]
          if (!messageState) return state

          const updatedMessageState = {
            ...messageState,
            blockingOperation: undefined,
          }

          // Clean up if no state remains
          const hasAnyState = updatedMessageState.copy || updatedMessageState.blockingOperation
          if (!hasAnyState) {
            const { [messageId]: _removed, ...remainingStates } = state.buttonStates
            return { buttonStates: remainingStates }
          }

          return {
            buttonStates: {
              ...state.buttonStates,
              [messageId]: updatedMessageState,
            },
          }
        })
      },
      failBlockingOperation: (messageId, error) => {
        set((state) => {
          const messageState = state.buttonStates[messageId]
          if (!messageState?.blockingOperation) return state

          return {
            buttonStates: {
              ...state.buttonStates,
              [messageId]: {
                ...messageState,
                blockingOperation: {
                  ...messageState.blockingOperation,
                  isLoading: false,
                  error,
                },
              },
            },
          }
        })
      },
      isMessageBlocked: (messageId) => {
        return !!get().buttonStates[messageId]?.blockingOperation?.isLoading
      },

      // Voice state (session-scoped, not persisted)
      readAloudEnabled: false,
      voiceSessionState: 'idle' as VoiceSessionState,
      editHistory: null,

      // Voice actions
      setReadAloud: (enabled) => {
        set({ readAloudEnabled: enabled })
      },
      setVoiceSessionState: (state) => {
        set({ voiceSessionState: state })
      },
      initEditHistory: (projectId, sessionId) => {
        set({ editHistory: createEditHistory({ projectId, sessionId }) })
      },
      snapshotOriginal: (messageId, content) => {
        set((state) => {
          if (!state.editHistory) return state
          if (messageId in state.editHistory.originalSnapshots) return state
          return {
            editHistory: {
              ...state.editHistory,
              originalSnapshots: {
                ...state.editHistory.originalSnapshots,
                [messageId]: content,
              },
            },
          }
        })
      },
      pushEdit: (params) => {
        set((state) => {
          if (!state.editHistory) return state
          return {
            editHistory: {
              ...state.editHistory,
              edits: [...state.editHistory.edits, createEditEntry(params)],
            },
          }
        })
      },
      popEdit: () => {
        const state = get()
        if (!state.editHistory || state.editHistory.edits.length === 0) return null

        const edits = state.editHistory.edits
        const lastEdit = edits[edits.length - 1]
        const messageId = lastEdit.messageId

        // Find the previous content for this message: walk backwards through remaining edits
        const remainingEdits = edits.slice(0, -1)
        let previousContent = state.editHistory.originalSnapshots[messageId] || ''
        for (let i = remainingEdits.length - 1; i >= 0; i--) {
          if (remainingEdits[i].messageId === messageId) {
            previousContent = remainingEdits[i].editedContent
            break
          }
        }

        set({
          editHistory: {
            ...state.editHistory,
            edits: remainingEdits,
          },
        })

        return { messageId, previousContent }
      },
      clearEditHistory: () => {
        set({ editHistory: null })
      },
    }),
    {
      name: 'conversation-storage',
      storage: createJSONStorage(getPersistStorage),
      partialize: (state) => ({
        projects: state.projects,
        activeProjectId: state.activeProjectId,
        messages: state.messages,
        buttonStates: state.buttonStates,
        _hasHydrated: state._hasHydrated,
      }),
      onRehydrateStorage: () => (state) => {
        if (state) {
          // Dates in persisted JSON are strings. Normalize to Date objects
          // and guard against malformed values to prevent runtime crashes.
          state.projects = normalizeProjects(state.projects)
          state.messages = normalizeMessages(state.messages)
          const persistedButtonStates =
            state.buttonStates && typeof state.buttonStates === 'object'
              ? state.buttonStates
              : {}

          // Clean up any loading states from previous session
          const cleanedButtonStates: Record<string, MessageButtonState> = {}
          Object.entries(persistedButtonStates).forEach(([messageId, buttonState]) => {
            const cleaned: MessageButtonState = {}

            // Don't restore loading operations (they won't complete after page reload)
            if (buttonState.blockingOperation && !buttonState.blockingOperation.isLoading) {
              cleaned.blockingOperation = buttonState.blockingOperation
            }

            // Don't restore copy states (they're temporary UI feedback)
            // Copy states are cleared after 2 seconds by component anyway

            if (cleaned.blockingOperation) {
              cleanedButtonStates[messageId] = cleaned
            }
          })

          state.buttonStates = cleanedButtonStates
          state.setHasHydrated(true)
        }
      },
    }
  )
)
