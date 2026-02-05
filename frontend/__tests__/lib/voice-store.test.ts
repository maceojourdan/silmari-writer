import { describe, it, expect, beforeEach } from 'vitest';
import { useConversationStore } from '@/lib/store';

describe('Voice Store Extensions', () => {
  beforeEach(() => {
    const { setState } = useConversationStore;
    setState({
      projects: [],
      activeProjectId: null,
      messages: {},
      buttonStates: {},
      readAloudEnabled: false,
      voiceSessionState: 'idle',
      editHistory: null,
    });
  });

  describe('readAloudEnabled', () => {
    it('should default to false', () => {
      const state = useConversationStore.getState();
      expect(state.readAloudEnabled).toBe(false);
    });

    it('should be togglable via setReadAloud', () => {
      const { setReadAloud } = useConversationStore.getState();
      setReadAloud(true);
      expect(useConversationStore.getState().readAloudEnabled).toBe(true);
      setReadAloud(false);
      expect(useConversationStore.getState().readAloudEnabled).toBe(false);
    });
  });

  describe('voiceSessionState', () => {
    it('should default to idle', () => {
      expect(useConversationStore.getState().voiceSessionState).toBe('idle');
    });

    it('should update via setVoiceSessionState', () => {
      const { setVoiceSessionState } = useConversationStore.getState();
      setVoiceSessionState('connecting');
      expect(useConversationStore.getState().voiceSessionState).toBe('connecting');
      setVoiceSessionState('connected');
      expect(useConversationStore.getState().voiceSessionState).toBe('connected');
    });
  });

  describe('editHistory', () => {
    it('should default to null', () => {
      expect(useConversationStore.getState().editHistory).toBeNull();
    });

    it('should initialize via initEditHistory', () => {
      const { initEditHistory } = useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');
      const history = useConversationStore.getState().editHistory;
      expect(history).toMatchObject({
        projectId: 'proj-1',
        sessionId: 'session-1',
        originalSnapshots: {},
        edits: [],
      });
    });

    it('should snapshot original content only once per message', () => {
      const { initEditHistory, snapshotOriginal } = useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');

      snapshotOriginal('msg-1', 'Original text');
      snapshotOriginal('msg-1', 'Should not overwrite');

      const history = useConversationStore.getState().editHistory!;
      expect(history.originalSnapshots['msg-1']).toBe('Original text');
    });

    it('should push edits to the edit stack', () => {
      const { initEditHistory, pushEdit } = useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');

      pushEdit({
        messageId: 'msg-1',
        editedContent: 'Edited version 1',
        editSummary: 'Changed intro',
      });

      const history = useConversationStore.getState().editHistory!;
      expect(history.edits).toHaveLength(1);
      expect(history.edits[0].editedContent).toBe('Edited version 1');
    });

    it('should pop the last edit and return previous content', () => {
      const { initEditHistory, snapshotOriginal, pushEdit, popEdit } =
        useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');
      snapshotOriginal('msg-1', 'Original');

      pushEdit({ messageId: 'msg-1', editedContent: 'Edit 1' });
      pushEdit({ messageId: 'msg-1', editedContent: 'Edit 2' });

      const result = popEdit();
      expect(result).toEqual({
        messageId: 'msg-1',
        previousContent: 'Edit 1',
      });

      const result2 = popEdit();
      expect(result2).toEqual({
        messageId: 'msg-1',
        previousContent: 'Original',
      });
    });

    it('should return null from popEdit when no edits remain', () => {
      const { initEditHistory, popEdit } = useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');

      expect(popEdit()).toBeNull();
    });

    it('should clear edit history', () => {
      const { initEditHistory, pushEdit, clearEditHistory } =
        useConversationStore.getState();
      initEditHistory('proj-1', 'session-1');
      pushEdit({ messageId: 'msg-1', editedContent: 'Edit 1' });

      clearEditHistory();
      expect(useConversationStore.getState().editHistory).toBeNull();
    });
  });
});
