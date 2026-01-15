'use client'

import { useConversationStore } from '@/lib/store'

export default function TestStorePage() {
  const {
    projects,
    activeProjectId,
    createProject,
    deleteProject,
    addMessage,
    getMessages,
    setActiveProject,
    clearMessages,
    getActiveProject,
    projectCount,
    hasMessages,
  } = useConversationStore()

  const activeMessages = activeProjectId ? getMessages(activeProjectId) : []
  const activeProject = getActiveProject()

  return (
    <div className="p-8 max-w-4xl mx-auto">
      <h1 className="text-2xl font-bold mb-4">Phase 6: Store Testing</h1>

      <div className="mb-6 p-4 bg-gray-100 rounded">
        <h2 className="text-lg font-semibold mb-2">Store State</h2>
        <p>
          <strong>Project Count:</strong> {projectCount()}
        </p>
        <p>
          <strong>Active Project ID:</strong> {activeProjectId || 'None'}
        </p>
        <p>
          <strong>Active Project Name:</strong> {activeProject?.name || 'None'}
        </p>
        <p>
          <strong>Has Messages (active):</strong>{' '}
          {activeProjectId ? String(hasMessages(activeProjectId)) : 'N/A'}
        </p>
      </div>

      <div className="mb-6">
        <h2 className="text-xl mb-2">Projects ({projects.length})</h2>
        <button
          onClick={() => createProject(`Project ${projects.length + 1}`)}
          className="px-4 py-2 bg-blue-500 text-white rounded hover:bg-blue-600"
        >
          Create Project
        </button>
        <ul className="mt-4 space-y-2">
          {projects.map((p) => (
            <li key={p.id} className="flex items-center gap-2">
              <button
                onClick={() => setActiveProject(p.id)}
                className={`px-4 py-2 rounded ${
                  activeProjectId === p.id
                    ? 'bg-blue-500 text-white'
                    : 'bg-gray-200 text-gray-800 hover:bg-gray-300'
                }`}
              >
                {p.name}
              </button>
              <button
                onClick={() => deleteProject(p.id)}
                className="px-3 py-1 bg-red-500 text-white text-sm rounded hover:bg-red-600"
              >
                Delete
              </button>
              <span className="text-sm text-gray-500">
                ({getMessages(p.id).length} messages)
              </span>
            </li>
          ))}
        </ul>
      </div>

      {activeProjectId && (
        <div className="mb-6">
          <h2 className="text-xl mb-2">Messages ({activeMessages.length})</h2>
          <div className="flex gap-2 mb-4">
            <button
              onClick={() =>
                addMessage(activeProjectId, {
                  role: 'user',
                  content: `User message ${activeMessages.length + 1}`,
                  timestamp: new Date(),
                })
              }
              className="px-4 py-2 bg-blue-500 text-white rounded hover:bg-blue-600"
            >
              Add User Message
            </button>
            <button
              onClick={() =>
                addMessage(activeProjectId, {
                  role: 'assistant',
                  content: `Assistant response ${activeMessages.length + 1}`,
                  timestamp: new Date(),
                })
              }
              className="px-4 py-2 bg-gray-500 text-white rounded hover:bg-gray-600"
            >
              Add Assistant Message
            </button>
            <button
              onClick={() => clearMessages(activeProjectId)}
              disabled={activeMessages.length === 0}
              className="px-4 py-2 bg-gray-200 text-gray-800 rounded hover:bg-gray-300 disabled:opacity-50 disabled:cursor-not-allowed"
            >
              Clear Messages
            </button>
          </div>
          <ul className="space-y-2">
            {activeMessages.map((m) => (
              <li
                key={m.id}
                className={`border p-3 rounded ${
                  m.role === 'user'
                    ? 'bg-blue-50 border-blue-200'
                    : 'bg-gray-50 border-gray-200'
                }`}
              >
                <div className="flex justify-between items-start">
                  <strong className={m.role === 'user' ? 'text-blue-600' : 'text-gray-600'}>
                    {m.role}:
                  </strong>
                  <span className="text-xs text-gray-400">
                    {m.timestamp instanceof Date
                      ? m.timestamp.toLocaleTimeString()
                      : new Date(m.timestamp).toLocaleTimeString()}
                  </span>
                </div>
                <p className="mt-1">{m.content}</p>
              </li>
            ))}
          </ul>
        </div>
      )}

      <div className="mt-8 p-4 bg-yellow-50 border border-yellow-200 rounded">
        <h3 className="font-semibold text-yellow-800">Persistence Test</h3>
        <p className="text-sm text-yellow-700 mt-2">
          Try refreshing the page (Ctrl+R / Cmd+R) or closing and reopening the browser tab.
          All projects and messages should persist.
        </p>
        <p className="text-sm text-yellow-700 mt-2">
          Check DevTools → Application → Local Storage → &quot;conversation-storage&quot; to
          see the stored data.
        </p>
      </div>
    </div>
  )
}
