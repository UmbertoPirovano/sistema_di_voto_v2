package gui;

import java.io.IOException;
import java.net.URL;
import java.util.List;
import java.util.Objects;
import java.util.ResourceBundle;

import javafx.event.ActionEvent;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.input.MouseEvent;
import javafx.scene.text.Text;
import javafx.stage.Stage;
import polls.Poll;
import system.SystemEvote;
import system.SystemEvoteObserver;
import users.Administrator;
import users.User;

public class AdminLogListController implements Initializable, SystemEvoteObserver {

	private List<String> logs;
	
    @FXML
    private Button backButton;

    @FXML
    private TableColumn<RowLog,String> colLog;

    @FXML
    private TableView<RowLog> logTable;

    @FXML
    private Button logoutButton;

    @FXML
    private Text nameSurnameLabel;

    @FXML
    private Text usernameLabel;

    @FXML
    void goBack(ActionEvent event) {
    	SystemEvote.getInstance().removeObserver(this);
    	try {
			logoutButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("AdminMenu.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Menù amministratore");
        	stage.setScene(new Scene(root, 900, 700));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
    }

    @FXML
    void logout(ActionEvent event) {
    	SystemEvote.getInstance().removeObserver(this);
    	SystemEvote.getInstance().logout();
    	showLoginWindow();
    }

    @FXML
    void mouse(MouseEvent event) {

    }

	@Override
	public void update(List<User> users, List<Poll> polls, List<String> logs) {
		Objects.requireNonNull(logs);
		this.logs = logs;
		System.out.println("Local logs list updated. Size: " + this.logs.size());
		refreshList();
	}
	
	private void refreshList() {
		logTable.getItems().clear();    	
    	for(String s : logs) {
    		RowLog rl = new RowLog(s);
    		logTable.getItems().add(rl);
    	}
	}

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		SystemEvote.getInstance().addObserver(this);		
		Administrator a = (Administrator) SystemEvote.getInstance().getSession().getUser();
    	nameSurnameLabel.setText(a.getUsername());
    	usernameLabel.setText("");
    	
    	colLog.setCellValueFactory(new PropertyValueFactory<>("Log"));
	}
	
	private void showLoginWindow() {
		try {
			logoutButton.getScene().getWindow().hide();
    		Parent root = FXMLLoader.load(getClass().getResource("LoginWindow.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Login");
        	stage.setScene(new Scene(root, 500, 390));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
	}

}
