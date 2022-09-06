package database;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Timestamp;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import users.Administrator;
import users.Elector;
import users.User;

public class UserDAOImpl implements UserDAO {

	private static UserDAO instance = null;
	private Connection connection;
	
	private UserDAOImpl() {
		connection = DatabaseConnection.getConnection();
	}
	
	public static UserDAO getInstance() {
		if(instance == null) {
			instance = new UserDAOImpl();
		}
		return instance;
	}
	
	
	public List<User> getAll() {
		List<User> users = new ArrayList<User>();
		try {
			PreparedStatement st = null;
			st = connection.prepareStatement("SELECT * FROM user;");
			ResultSet res = st.executeQuery();
			while (res.next()) {
				User u = null;
				String username = res.getString("username");
				String password = res.getString("password");
				if(res.getBoolean("admin")) {
					u = new Administrator(username, password);
				}else {
					String name = res.getString("name");
					String surname = res.getString("surname");
					u = new Elector(username, password, name, surname);
				}
				users.add(u);
			}
		} catch (SQLException se) {
			se.printStackTrace();
		}		
		return users;
	}

	public User getUser(String username) {
		Objects.requireNonNull(username);
		List<User> users = getAll();
		for(User u : users) {
			if(u.getUsername().equals(username))
				return u;
		}
		throw new IllegalArgumentException("Utente non trovato.");
	}
	
	/**
	 * Esegue le operazioni specifiche per aggiungere un utente di tipo Elector al database.
	 * @param e: oggetto di tipo Elector che rappresenta l'utente che vogliamo registrare
	 * @param password: la password con cui registrare l'utente
	 */
	private void addElector(Elector e, String password) {		
		Objects.requireNonNull(e);
		Objects.requireNonNull(password);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("INSERT INTO user(username, password, name, surname) VALUES (?,SHA2(?,512),?,?);");
			st.setString(1, e.getUsername());
			st.setString(2, password);
			st.setString(3, e.getName());
			st.setString(4, e.getSurname());
			
			st.executeUpdate();
		} catch (SQLException exc) {
			exc.printStackTrace();
		}		
	}
	
	/**
	 * Esegue le operazioni specifiche per aggiungere un utente di tipo Administrator al database.
	 * @param a: oggetto di tipo Administrator che rappresenta l'utente che vogliamo registrare
	 * @param password: la password con cui registrare l'utente
	 */
	private void addAdministrator(Administrator a, String password) {
		Objects.requireNonNull(a);
		Objects.requireNonNull(password);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("INSERT INTO user(username, password, admin) VALUES (?,SHA2(?,512),1);");
			st.setString(1, a.getUsername());
			st.setString(2, password);
			
			st.executeUpdate();
		} catch (SQLException exc) {
			exc.printStackTrace();
		}
	}
	
	public void addUser(User u, String password) {
		Objects.requireNonNull(u);
		Objects.requireNonNull(password);
		if(u instanceof Elector) {
			addElector((Elector) u, password);
		}else if(u instanceof Administrator) {
			addAdministrator((Administrator) u, password);
		}else {
			throw new IllegalArgumentException("Tipo di utente non supportato");
		}
	}
	
	public void deleteUser(User u) {
		Objects.requireNonNull(u);
		PreparedStatement st = null;
		try {
			st = connection.prepareStatement("DELETE FROM user WHERE user.username = BINARY ?;");
			st.setString(1, u.getUsername());
			
			st.executeUpdate();
		} catch (SQLException e) {
			e.printStackTrace();
		}		
	}

	public boolean checkCredentials(String username, String password) {
		Objects.requireNonNull(username);
		Objects.requireNonNull(password);
		try {
			PreparedStatement st = null;
			st = connection.prepareStatement("SELECT * FROM user"
					+ " WHERE username = ? AND password = SHA2(?, 512);");
			st.setString(1, username);
			st.setString(2, password);
			ResultSet res = st.executeQuery();
			if(res.next()) return true;
		} catch (SQLException se) {
			se.printStackTrace();
		}		
		return false;
	}

	public User login(String username, String password) {
		Objects.requireNonNull(username);
		Objects.requireNonNull(password);
		if(checkCredentials(username, password))
			return getUser(username);
		throw new IllegalArgumentException("Username o password errati.");
	}

	@Override
	public void addLogEntry(User user, String azione) {
		Objects.requireNonNull(user);
		Objects.requireNonNull(azione);
		
		List<User> users = getAll();
		for(User u : users) {
			if(u.getUsername().equals(user.getUsername())) {
				try {
					PreparedStatement st = connection.prepareStatement("INSERT INTO log(user, azione, timestamp) VALUES (?,?,?);");
					st.setString(1, user.getUsername());
					st.setString(2, azione);
					st.setTimestamp(3, new Timestamp(System.currentTimeMillis()));
				}catch(SQLException e) {
					e.printStackTrace();
				}
				return;
			}
		}
		
		throw new IllegalArgumentException("Username non trovato");
	}

}
