package system;

import users.Administrator;
import users.User;

public class SessionAdministrator extends Session{

	public SessionAdministrator(User user) {
		super(user);
		if(!(user instanceof Administrator)) {
			throw new IllegalArgumentException("Una sessione di tipo SessionAdministrator "
					+ "può essere istanziata solo fornendo come argomento un oggetto di tipo Administrator.");
		}
	}
}
