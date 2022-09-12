package gui;

import java.io.IOException;
import java.net.URL;
import java.util.Collections;
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

public class AdminPollListController implements Initializable, SystemEvoteObserver {
	
	private List<Poll> polls;
	
    @FXML
    private Button addUserButton;

    @FXML
    private Button backButton;

    @FXML
    private TableColumn<RowPoll, String> col_name;
    
    @FXML
    private TableColumn<RowPoll, String> col_type;

    @FXML
    private TableColumn<RowPoll, String> col_startDate;

    @FXML
    private TableColumn<RowPoll, String> col_endDate;
    
    @FXML
    private TableColumn<RowPoll, String> col_action;
    
    @FXML
    private TableColumn<RowPoll, String> col_status;

    @FXML
    private Button logoutButton;

    @FXML
    private Text nameSurnameLabel;

    @FXML
    private Text usernameLabel;

    @FXML
    private TableView<RowPoll> votazioniTable;

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

    @FXML
    void showPollEditor(ActionEvent event) {
    	try {
    		Parent root = FXMLLoader.load(getClass().getResource("AdminPollEditor.fxml"));
            Stage stage = new Stage();
        	stage.setTitle("Sistema di voto elettronico - Editor votazioni");
        	stage.setScene(new Scene(root, 700, 600));
        	stage.setResizable(false);
        	stage.show();
		}catch (IOException e) {
			System.out.println(e.getMessage());
		}
    }

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		SystemEvote.getInstance().addObserver(this);		
		Administrator a = (Administrator) SystemEvote.getInstance().getSession().getUser();
    	nameSurnameLabel.setText(a.getUsername());
    	usernameLabel.setText("");
    	
    	col_name.setCellValueFactory(new PropertyValueFactory<>("name"));
    	col_type.setCellValueFactory(new PropertyValueFactory<>("type"));
    	col_startDate.setCellValueFactory(new PropertyValueFactory<>("startDate"));
    	col_endDate.setCellValueFactory(new PropertyValueFactory<>("endDate"));
    	col_status.setCellValueFactory(new PropertyValueFactory<>("status"));
    	col_action.setCellValueFactory(new PropertyValueFactory<>("buttonBar"));		
	}
	
	@Override
	public void update(List<User> users, List<Poll> polls,List<String> logs) {
		Objects.requireNonNull(polls);
		this.polls = polls;
		System.out.println("Local poll list updated. Size: " + this.polls.size());
		refreshList();
	}
	
	private void refreshList() {
		votazioniTable.getItems().clear();    	
    	for(Poll p : polls) {
    		RowPoll rv = new RowPoll(p);
    		votazioniTable.getItems().add(rv);
    	}
    	Collections.sort(votazioniTable.getItems());
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