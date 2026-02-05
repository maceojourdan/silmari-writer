import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest'
import { act, renderHook } from '@testing-library/react'
import { useConversationStore } from '@/lib/store'

// Mock localStorage
const localStorageMock = (() => {
  let store: Record<string, string> = {}
  return {
    getItem: (key: string) => store[key] || null,
    setItem: (key: string, value: string) => {
      store[key] = value
    },
    removeItem: (key: string) => {
      delete store[key]
    },
    clear: () => {
      store = {}
    },
    get length() {
      return Object.keys(store).length
    },
    key: (index: number) => Object.keys(store)[index] || null,
  }
})()

Object.defineProperty(window, 'localStorage', {
  value: localStorageMock,
})

// Mock crypto.randomUUID
let uuidCounter = 0
vi.stubGlobal('crypto', {
  randomUUID: () => `test-uuid-${++uuidCounter}`,
})

describe('useConversationStore', () => {
  beforeEach(() => {
    // Clear both mock and real localStorage
    localStorageMock.clear()
    window.localStorage.clear()
    uuidCounter = 0
    // Reset the store state
    useConversationStore.setState({
      projects: [],
      activeProjectId: null,
      messages: {},
    })
  })

  afterEach(() => {
    vi.clearAllMocks()
  })

  describe('Project CRUD Operations', () => {
    it('createProject creates new project with unique ID', () => {
      const { result } = renderHook(() => useConversationStore())

      let projectId: string
      act(() => {
        projectId = result.current.createProject('My Project')
      })

      expect(projectId!).toBe('test-uuid-1')
      expect(result.current.projects).toHaveLength(1)
      expect(result.current.projects[0]).toMatchObject({
        id: 'test-uuid-1',
        name: 'My Project',
      })
      expect(result.current.projects[0].createdAt).toBeInstanceOf(Date)
      expect(result.current.projects[0].updatedAt).toBeInstanceOf(Date)
    })

    it('createProject sets the new project as active', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('My Project')
      })

      expect(result.current.activeProjectId).toBe('test-uuid-1')
    })

    it('createProject creates multiple projects with unique IDs', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.createProject('Project 2')
        result.current.createProject('Project 3')
      })

      expect(result.current.projects).toHaveLength(3)
      expect(result.current.projects[0].id).toBe('test-uuid-1')
      expect(result.current.projects[1].id).toBe('test-uuid-2')
      expect(result.current.projects[2].id).toBe('test-uuid-3')
    })

    it('deleteProject removes project from list', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.createProject('Project 2')
      })

      expect(result.current.projects).toHaveLength(2)

      act(() => {
        result.current.deleteProject('test-uuid-1')
      })

      expect(result.current.projects).toHaveLength(1)
      expect(result.current.projects[0].name).toBe('Project 2')
    })

    it('deleteProject removes associated messages', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'Hello',
          timestamp: new Date(),
        })
      })

      expect(result.current.getMessages('test-uuid-1')).toHaveLength(1)

      act(() => {
        result.current.deleteProject('test-uuid-1')
      })

      expect(result.current.getMessages('test-uuid-1')).toHaveLength(0)
    })

    it('deleteProject switches active to first remaining project', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.createProject('Project 2')
        result.current.setActiveProject('test-uuid-2')
      })

      expect(result.current.activeProjectId).toBe('test-uuid-2')

      act(() => {
        result.current.deleteProject('test-uuid-2')
      })

      expect(result.current.activeProjectId).toBe('test-uuid-1')
    })

    it('deleteProject sets activeProjectId to null when last project deleted', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
      })

      act(() => {
        result.current.deleteProject('test-uuid-1')
      })

      expect(result.current.activeProjectId).toBeNull()
      expect(result.current.projects).toHaveLength(0)
    })

    it('updateProject modifies project properties', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Original Name')
      })

      const originalUpdatedAt = result.current.projects[0].updatedAt

      act(() => {
        result.current.updateProject('test-uuid-1', { name: 'Updated Name' })
      })

      expect(result.current.projects[0].name).toBe('Updated Name')
      // updatedAt should be a valid date (may be same or later)
      expect(result.current.projects[0].updatedAt).toBeInstanceOf(Date)
      expect(result.current.projects[0].updatedAt.getTime()).toBeGreaterThanOrEqual(
        originalUpdatedAt.getTime()
      )
    })

    it('updateProject does not affect other projects', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.createProject('Project 2')
      })

      act(() => {
        result.current.updateProject('test-uuid-1', { name: 'Updated Project 1' })
      })

      expect(result.current.projects[0].name).toBe('Updated Project 1')
      expect(result.current.projects[1].name).toBe('Project 2')
    })

    it('setActiveProject changes the active project', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.createProject('Project 2')
      })

      // Last created is active
      expect(result.current.activeProjectId).toBe('test-uuid-2')

      act(() => {
        result.current.setActiveProject('test-uuid-1')
      })

      expect(result.current.activeProjectId).toBe('test-uuid-1')
    })
  })

  describe('Message Operations', () => {
    it('addMessage adds message to project', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'Hello',
          timestamp: new Date(),
        })
      })

      const messages = result.current.getMessages('test-uuid-1')
      expect(messages).toHaveLength(1)
      expect(messages[0].content).toBe('Hello')
      expect(messages[0].role).toBe('user')
      expect(messages[0].id).toBe('test-uuid-2') // Second UUID generated
    })

    it('addMessage adds messages in correct order', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'First',
          timestamp: new Date(),
        })
        result.current.addMessage('test-uuid-1', {
          role: 'assistant',
          content: 'Second',
          timestamp: new Date(),
        })
        result.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'Third',
          timestamp: new Date(),
        })
      })

      const messages = result.current.getMessages('test-uuid-1')
      expect(messages).toHaveLength(3)
      expect(messages[0].content).toBe('First')
      expect(messages[1].content).toBe('Second')
      expect(messages[2].content).toBe('Third')
    })

    it('getMessages returns empty array for non-existent project', () => {
      const { result } = renderHook(() => useConversationStore())

      const messages = result.current.getMessages('non-existent-id')
      expect(messages).toEqual([])
    })

    it('clearMessages removes all messages from project', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'Hello',
          timestamp: new Date(),
        })
        result.current.addMessage('test-uuid-1', {
          role: 'assistant',
          content: 'Hi',
          timestamp: new Date(),
        })
      })

      expect(result.current.getMessages('test-uuid-1')).toHaveLength(2)

      act(() => {
        result.current.clearMessages('test-uuid-1')
      })

      expect(result.current.getMessages('test-uuid-1')).toHaveLength(0)
    })

    it('clearMessages does not affect other projects', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.createProject('Project 2')
        result.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'Hello Project 1',
          timestamp: new Date(),
        })
        result.current.addMessage('test-uuid-2', {
          role: 'user',
          content: 'Hello Project 2',
          timestamp: new Date(),
        })
      })

      act(() => {
        result.current.clearMessages('test-uuid-1')
      })

      expect(result.current.getMessages('test-uuid-1')).toHaveLength(0)
      expect(result.current.getMessages('test-uuid-2')).toHaveLength(1)
    })

    it('messages are isolated between projects', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.createProject('Project 2')
        result.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'Message for Project 1',
          timestamp: new Date(),
        })
        result.current.addMessage('test-uuid-2', {
          role: 'user',
          content: 'Message for Project 2',
          timestamp: new Date(),
        })
      })

      const messages1 = result.current.getMessages('test-uuid-1')
      const messages2 = result.current.getMessages('test-uuid-2')

      expect(messages1).toHaveLength(1)
      expect(messages1[0].content).toBe('Message for Project 1')

      expect(messages2).toHaveLength(1)
      expect(messages2[0].content).toBe('Message for Project 2')
    })
  })

  describe('Selectors', () => {
    it('getActiveProject returns the active project', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.createProject('Project 2')
      })

      expect(result.current.getActiveProject()?.name).toBe('Project 2')

      act(() => {
        result.current.setActiveProject('test-uuid-1')
      })

      expect(result.current.getActiveProject()?.name).toBe('Project 1')
    })

    it('getActiveProject returns undefined when no active project', () => {
      const { result } = renderHook(() => useConversationStore())

      expect(result.current.getActiveProject()).toBeUndefined()
    })

    it('getActiveMessages returns messages for active project', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'Hello',
          timestamp: new Date(),
        })
      })

      const activeMessages = result.current.getActiveMessages()
      expect(activeMessages).toHaveLength(1)
      expect(activeMessages[0].content).toBe('Hello')
    })

    it('getActiveMessages returns empty array when no active project', () => {
      const { result } = renderHook(() => useConversationStore())

      expect(result.current.getActiveMessages()).toEqual([])
    })

    it('hasMessages returns true when project has messages', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
        result.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'Hello',
          timestamp: new Date(),
        })
      })

      expect(result.current.hasMessages('test-uuid-1')).toBe(true)
    })

    it('hasMessages returns false when project has no messages', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
      })

      expect(result.current.hasMessages('test-uuid-1')).toBe(false)
    })

    it('hasMessages returns false for non-existent project', () => {
      const { result } = renderHook(() => useConversationStore())

      expect(result.current.hasMessages('non-existent')).toBe(false)
    })

    it('projectCount returns correct count', () => {
      const { result } = renderHook(() => useConversationStore())

      expect(result.current.projectCount()).toBe(0)

      act(() => {
        result.current.createProject('Project 1')
      })

      expect(result.current.projectCount()).toBe(1)

      act(() => {
        result.current.createProject('Project 2')
        result.current.createProject('Project 3')
      })

      expect(result.current.projectCount()).toBe(3)
    })
  })

  describe('Persistence', () => {
    it('store has persist middleware configured', () => {
      // Verify that the store has the persist API available
      expect(useConversationStore.persist).toBeDefined()
      expect(useConversationStore.persist.getOptions).toBeDefined()

      // Verify the storage name is correct
      const options = useConversationStore.persist.getOptions()
      expect(options.name).toBe('conversation-storage')
    })

    it('state survives across multiple hook renders', () => {
      // First render - create project
      const { result: result1 } = renderHook(() => useConversationStore())

      act(() => {
        result1.current.createProject('Persistent Project')
        result1.current.addMessage('test-uuid-1', {
          role: 'user',
          content: 'Test message',
          timestamp: new Date(),
        })
      })

      // Second render - state should still be there (same store)
      const { result: result2 } = renderHook(() => useConversationStore())

      expect(result2.current.projects).toHaveLength(1)
      expect(result2.current.projects[0].name).toBe('Persistent Project')
      expect(result2.current.getMessages('test-uuid-1')).toHaveLength(1)
    })

    it('persist.setOptions returns configuration', () => {
      const options = useConversationStore.persist.getOptions()

      expect(options).toHaveProperty('name')
      expect(options.name).toBe('conversation-storage')
    })
  })

  describe('Edge Cases', () => {
    it('handles deleting non-existent project gracefully', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        result.current.createProject('Project 1')
      })

      // Should not throw
      act(() => {
        result.current.deleteProject('non-existent-id')
      })

      expect(result.current.projects).toHaveLength(1)
    })

    it('handles updating non-existent project gracefully', () => {
      const { result } = renderHook(() => useConversationStore())

      // Should not throw
      act(() => {
        result.current.updateProject('non-existent-id', { name: 'New Name' })
      })

      expect(result.current.projects).toHaveLength(0)
    })

    it('handles adding message to non-existent project gracefully', () => {
      const { result } = renderHook(() => useConversationStore())

      // Should not throw - creates messages array for the project
      act(() => {
        result.current.addMessage('non-existent-id', {
          role: 'user',
          content: 'Hello',
          timestamp: new Date(),
        })
      })

      // Messages are stored even for non-existent projects (orphaned messages)
      expect(result.current.getMessages('non-existent-id')).toHaveLength(1)
    })

    it('handles clearing messages for non-existent project gracefully', () => {
      const { result } = renderHook(() => useConversationStore())

      // Should not throw
      act(() => {
        result.current.clearMessages('non-existent-id')
      })

      expect(result.current.getMessages('non-existent-id')).toHaveLength(0)
    })

    it('handles rapid project creation and deletion', () => {
      const { result } = renderHook(() => useConversationStore())

      act(() => {
        for (let i = 0; i < 10; i++) {
          result.current.createProject(`Project ${i}`)
        }
      })

      expect(result.current.projects).toHaveLength(10)

      act(() => {
        for (let i = 1; i <= 5; i++) {
          result.current.deleteProject(`test-uuid-${i}`)
        }
      })

      expect(result.current.projects).toHaveLength(5)
    })
  })
})
