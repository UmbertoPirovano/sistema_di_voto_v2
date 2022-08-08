package system;

import users.Elector;
import users.User;

public class SessionElector extends Session {

	public SessionElector(User user) {
		super(user);
		if(!(user instanceof Elector))
			throw new IllegalArgumentException("Una sessione di tipo SessionElector può "
					+ "essere istanziata solo fornendo come argomento un oggetto di tipo Elector");
	}

}
