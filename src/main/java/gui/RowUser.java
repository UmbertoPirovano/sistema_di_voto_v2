package gui;

import java.util.Objects;

import javafx.beans.property.SimpleStringProperty;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonBar;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.stage.Stage;
import system.SystemEvote;
import users.Administrator;
import users.Elector;
import users.User;

public class RowUser implements Comparable<RowUser> {
	private final User user;
	private final SimpleStringProperty username;
	private final SimpleStringProperty name;
	private final SimpleStringProperty surname;
	private final SimpleStringProperty type;
	private ButtonBar buttonBar;
	
	public RowUser(User u) {
		user = Objects.requireNonNull(u);
		username = new SimpleStringProperty(user.getUsername());
		if(user instanceof Elector) {
			Elector e = (Elector) user;
			type = new SimpleStringProperty("Elettore");
			name = new SimpleStringProperty(e.getName());
			surname = new SimpleStringProperty(e.getSurname());
		}else if(user instanceof Administrator) {
			type = new SimpleStringProperty("Amministratore");
			name = new SimpleStringProperty("-");
			surname = new SimpleStringProperty("-");
		}else {
			throw new IllegalArgumentException("Tipo non supportato.");
		}
		
		Button deleteUserButton = new Button("");
		ImageView deletePng = new ImageView(new Image(getClass().getResource("delete.png").toString()));
		deletePng.setFitHeight(20);
		deletePng.setPreserveRatio(true);
		deleteUserButton.setGraphic(deletePng);
		deleteUserButton.setOnAction(event -> deleteUser());
		
		buttonBar = new ButtonBar();
		buttonBar.getButtons().addAll(deleteUserButton);
	}

	private void deleteUser() {
		try {
			SystemEvote.getInstance().deleteUser(user);
		}catch(IllegalArgumentException e) {
			showErrorMessage("errore\n" + e.getMessage());
		}
	}

	public User getUser() {
		return user;
	}
	
	public String getUsername() {
		return username.get();
	}
	
	public String getName() {
		return name.get();
	}
	
	public String getSurname() {
		return surname.get();
	}
	
	public String getType() {
		return type.get();
	}
	
	public ButtonBar getButtonBar() {
		return buttonBar;
	}
	
	private void showErrorMessage(String s) {
		Objects.requireNonNull(s);
		String msg = "ERROR:\n\n";
		msg += s;
		try {
			FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralMessage.fxml"));
    		GeneralMessageController controller = new GeneralMessageController(msg);
    		loader.setController(controller);
    		Parent root = loader.load();
            Stage stage = new Stage();
        	stage.setTitle("ERROR");
        	stage.setScene(new Scene(root, 600, 400));
        	stage.setResizable(false);
        	stage.show();
		} catch (Exception e) {
			showErrorMessage(e.getMessage());
			e.printStackTrace();
		}
	}

	@Override
	public int compareTo(RowUser o) {
		return this.getUsername().compareToIgnoreCase(o.getUsername());
	}
}
