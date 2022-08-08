package system;

import java.util.List;

import polls.Poll;
import users.User;

public interface SystemEvoteObserver {
	
	/**
	 * Aggiorna le informazioni contenute in this con quelle ricevute
	 * come argomento.
	 * @param users: una lista di oggetti User
	 * @param polls: una lista di oggetti Poll
	 */
	public void update(List<User> users, List<Poll> polls);
	
}
