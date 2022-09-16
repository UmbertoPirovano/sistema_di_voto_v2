package database;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.Objects;

public class DatabaseConnection {
	private static String database = "sistema_di_voto";
	private static String user = "root";
	private static String password = "";
	
	public static Connection getConnection() {
		Connection c = null;
		try {
			c = DriverManager.getConnection(getPath());
		} catch (SQLException ex) {
			ex.printStackTrace();
		}
		return c;
	}
	
	private static String getPath() {
		return "jdbc:mysql://localhost/" + database + "?user=" + user + "&password=" + password;
	}
	
	public static void setParams(String db, String usr, String pwd) {
		database = Objects.requireNonNull(db);
		user = Objects.requireNonNull(usr);
		password = Objects.requireNonNull(pwd);		
	}
	
	public static void setDatabase(String db) {
		database = Objects.requireNonNull(db);
	}
	
	public static void setUser(String usr) {
		user = Objects.requireNonNull(usr);
	}
	
	public static void setPassword(String pwd) {
		password = Objects.requireNonNull(pwd);
	}
	
	public static String getDatabase() {
		return database;
	}
	
	public static String getUser() {
		return user;
	}
}
