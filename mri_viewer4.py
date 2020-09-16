from tkinter import *
from tkinter.filedialog import *
import os
import numpy as np
import pydicom as dcm
import pydicom.uid
from pydicom.dataset import Dataset, FileDataset
import re
import glob
from itertools import compress
import datetime
import time
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure


menu_font = ('Helvetica', 12)
base_font = ('Helvetica', 12)
cond_interval = 23


def str_extract(string, text):
    extract = re.search(string, text)
    if extract is None:
        matching = None
    else:
        matching = extract.group()
    return matching


widget_width = 1500
widget_height = int(widget_width * 0.65)


class ViewerMRI:
    def __init__(self):
        self.gui = Tk()
        self.gui.title('Texture extractor for MRI Image v1.4')
        self.gui.call('tk', 'scaling', 1.2)
        ws, hs = self.gui.winfo_screenwidth(), self.gui.winfo_screenheight()

        w, h = widget_width, widget_height
        x, y = (ws / 6) - (w / 6), (hs / 2) / (h / 2)
        self.gui.geometry('%dx%d+%d+%d' % (w, h, x, y))

        self.gui.minsize(600, 390)
        self.gui.resizable(True, True)

        self.set_wd, self.set_dir = None, None  # select set directory using askdirectory & set directory
        self.save_wd, self.save_dir = None, None  # select save directory using askdirectory & save directory

        self.cond_width = 72

        self.grid_color = 'dodgerblue'  # default horizontal & vertical line color
        self.patch_color = 'darkorange'  # default patch border color

        self.study_num, self.slice_num = None, None  # study & slice index

        self.div_num = 8  # default number of grids
        self.d_interval = 64  # default grid interval
        self.dw_rest, self.dh_rest = 0, 0  # grid adjustment variable
        self.x_drags, self.y_drags = [], []
        self.adjust_type = None

        self.image_dpi = 32  # default dpi
        self.f_size = 32  # figure size, set self.image_dpi * self.f_size = 512 (MRI image row & column)

        self.is_grid = False  # whether there is a grid in the image
        self.is_adjust_grid = False  # whether grid is being adjusted

        self.patch_array = {}  # save patch images
        self.select_patches = {}  # display checked grid area
        self.is_patch = {}  # whether check patch patch in the grid
        self.is_patch_w, self.is_patch_h = {}, {}  # whether check patch in the grid
        self.patch_num = 0  # the number of patches checked in the image

        self.study_index = IntVar()
        self.study_index.set(-1)
        self.sop_index = IntVar()
        self.sop_index.set(-1)

        self.menu_bar = Menu(self.gui)
        file_menu = Menu(self.menu_bar, tearoff=0)
        file_menu.add_command(label='Open Folder...', font=menu_font, command=self.open_folder)
        file_menu.add_command(label='Open Directory...', font=menu_font, command=self.open_directory)
        file_menu.add_command(label='Quit', font=menu_font, command=self.quit)
        self.menu_bar.add_cascade(label='File', font=menu_font, menu=file_menu)

        export_menu = Menu(self.menu_bar, tearoff=0)
        export_menu.add_command(label='Select Save Folder...', font=menu_font, command=self.save_folder)
        export_menu.add_command(label='Export Result...', font=menu_font, command=self.export_result)
        self.menu_bar.add_cascade(label='Export', font=menu_font, menu=export_menu)

        help_menu = Menu(self.menu_bar, tearoff=0)
        help_menu.add_command(label='Help...', font=menu_font, command=self.viewer_help)
        help_menu.add_command(label='Info...', font=menu_font, command=self.information)
        self.menu_bar.add_cascade(label='Help', font=menu_font, menu=help_menu)

        self.gui.config(menu=self.menu_bar)

        self.frame10 = Frame(self.gui)
        self.study_desc = Label(self.frame10, width=self.cond_width, text='Study Description',
                                background='midnightblue', foreground='snow', font=base_font)
        self.study_desc.grid(row=0, column=0)

        self.study_check = Label(self.frame10, width=self.cond_width, text='Study Check',
                                  background='royalblue', foreground='snow', font=base_font)
        self.study_check.grid(row=1, column=0)

        self.coord_window = Label(self.frame10, width = self.cond_width, text="Coordinates: ",
                                   background='lightskyblue', foreground='black', font=base_font)
        self.coord_window.grid(row=2, column=0)

        self.save_path = Label(self.frame10, width=self.cond_width, text='Save path required',
                               background='aqua', foreground='black', font=base_font)
        self.save_path.grid(row=3, column=0)

        self.slice_desc = Label(self.frame10, width=self.cond_width, text='Image Description',
                                background='indianred', foreground='snow', font=base_font)
        self.slice_desc.grid(row=4, column=0)

        self.slice_check = Label(self.frame10, width=self.cond_width, text='Series Check',
                                  background='deeppink', foreground='snow', font=base_font)
        self.slice_check.grid(row=5, column=0)

        self.grid_select = Label(self.frame10, width = self.cond_width, text="Grid select",
                                 background='pink', foreground='black', font=base_font)
        self.grid_select.grid(row=6, column=0)

        self.cond_window = Label(self.frame10, width=self.cond_width, text='Condition window',
                                 background='mistyrose', foreground='black', font=base_font)
        self.cond_window.grid(row=7, column=0)

        self.grid_adjust_button = Button(self.frame10, width=self.cond_width, text='Grid Adjust', font=base_font,
                                  background='navy', foreground='snow', command=self.adjust_grid)
        self.grid_adjust_button.grid(row=8, column=0)

        self.grid_button = Button(self.frame10, width = self.cond_width, text='Add Grid', font=base_font,
                                  background='firebrick', foreground='snow', command=self.add_grid)
        self.grid_button.grid(row=9, column=0)

        self.frame10.pack(side=LEFT, anchor='nw', expand=True)

        self.f12_study_prev = Button(self.gui, text='Study Prev', font=base_font, height=1, width=10,
                                     command=self.study_prev)
        self.f12_study_prev.place(x=140, y=11.25 * cond_interval + 2)

        self.f12_study_next = Button(self.gui, text='Study Next', font=base_font, height=1, width=10,
                                     command=self.study_next)
        self.f12_study_next.place(x=320, y=11.25 * cond_interval + 2)

        self.f12_prev = Button(self.gui, text="Image Prev", font=base_font, height=1, width=10,
                               command=self.slice_prev)
        self.f12_prev.place(x=230, y=10 * cond_interval + 2)

        self.f12_next = Button(self.gui, text="Image Next", font=base_font, height=1, width=10,
                               command=self.slice_next)
        self.f12_next.place(x=230, y=11.25 * cond_interval + 2)

        self.frame13 = Frame(self.gui, height=600, width=600)
        self.canvas = None
        self.frame13.pack(fill=BOTH, anchor='w', expand=True)

        self.gui.bind("<a>", self.adjust_grid_key)

    def quit(self):
        self.gui.quit()

    def open_folder(self):
        self.set_wd = askdirectory(title='Open Folder', mustexist=1)

        if self.set_wd:
            self.set_dir = self.set_wd
            is_dcm = glob.glob(self.set_dir + '/*.dcm')
            dcm_file_num = len(is_dcm)

            if dcm_file_num < 1:
                self.error_box('Error! DICOM file does not exist in this folder.')
                return
            else:
                self.dcm_folder = [self.set_dir]  # convert string to list
                self.study_index.set(1)
                self.sop_index.set(1)
                self.study_num = len(self.dcm_folder)  # must be 1
                assert self.study_num == 1
                self.go_to_image(self.study_index, self.sop_index)
                self.image_setting(self.study_index, self.sop_index)
        else:
            if self.set_dir is None:
                self.set_wd = None
            else:
                pass

    def find_folder_dcm(self, tree_dir, folder):
        dcm_path = glob.glob(os.path.join(tree_dir, folder) + '/*.dcm')
        return len(dcm_path)

    def open_directory(self):
        self.set_wd = askdirectory(title='Open Directory', mustexist=1)

        if self.set_wd:
            self.set_dir = self.set_wd
            folder_list = sorted(os.listdir(self.set_dir))
            all_folder = [self.find_folder_dcm(self.set_dir, folder) for folder in folder_list]
            dcm_folders_bool = [n != 0 for n in all_folder]
            dcm_folder = list(compress(folder_list, dcm_folders_bool))

            if len(dcm_folder) < 1:
                self.error_box('Error! Please check if there are DICOM files in the folders of the selected directory')
                return
            else:
                self.dcm_folder = list(map(lambda x: self.set_dir+'/'+x, dcm_folder))

                self.study_index.set(1)
                self.sop_index.set(1)
                self.study_num = len(self.dcm_folder)

                self.go_to_image(self.study_index, self.sop_index)
                self.image_setting(self.study_index, self.sop_index)
        else:
            if self.set_dir is None:
                self.set_wd = None
            else:
                pass

    def save_folder(self):
        self.save_wd = askdirectory(title='Select Save Folder', mustexist=1)

        if self.save_wd:
            self.save_dir = self.save_wd
            self.save_path.config(text='Save dir: ' + self.save_dir)
        else:
            if self.save_dir is None:
                self.save_wd = None
            else:
                pass

    def export_result(self):
        if self.canvas is not None:
            if self.save_dir is not None:
                if self.patch_num == 0:
                    self.error_box('Error! There are no saved patches.')
                else:
                    count = 0
                    for pw in range(0, len(self.is_patch_w)):
                        for ph in range(0, len(self.is_patch_h)):
                            patch_idx = '_'.join([str(pw - 1), str(ph - 1)])
                            if self.is_patch[patch_idx]:
                                folder_dcm = '_'.join([self.folder_basename, re.sub('.dcm', '', self.dcm_name)])
                                grid_index = '_%03d_%03d_%03d_%03d_%03d' % \
                                             (self.d_interval, self.dw_rest, self.dh_rest, pw, ph)
                                save_name = folder_dcm + grid_index + '.dcm'

                                save_file = os.path.join(self.save_dir, save_name)
                                self.write_dcm(self.patch_array[patch_idx], pw, ph, save_file)
                                count += 1

                    self.cond_window.config(text='%d ' % count + self.cond_sentence(count) + ' saved')
            else:
                self.error_box('Error! Please set a save path first.')
        else:
            self.error_box('Error! Please upload image.')

    def viewer_help(self):
        help_popup = Toplevel()
        help_popup.geometry('600x300')
        help_text = Text(help_popup, font=base_font)
        help_text.insert(INSERT, '- Upload folder in .dcm file: File menu -> Select Folder... \n')
        help_text.insert(INSERT, '- Move Next dcm file: ↓ or spacebar \n')
        help_text.insert(INSERT, '- Move Previous dcm file: ↑ \n')
        help_text.insert(INSERT, '- Move Next study: → \n')
        help_text.insert(INSERT, '- Move Previous study: ← \n')
        help_text.insert(INSERT, "- Adjust grid interval: 'Grid Adjust' button click or 'g' key \n")
        help_text.insert(INSERT, "- Add grid: 'Add grid' button click or 'a' key \n")
        help_text.insert(INSERT, '- Select grid: mouse click on that area \n')
        help_text.insert(INSERT, '- Delete grid: mouse click again on the selected area \n')
        help_text.insert(INSERT, '- Specify folder to save:  Select Save Folder... \n')
        help_text.insert(INSERT, '- Export result: Export menu -> Export Result...')
        help_text.pack()

    def information(self):
        self.info_popup = Toplevel()
        self.info_popup.geometry('300x40')
        info_label = Label(self.info_popup, text='MRI image grid addition and storage program' + '\n' +
                                                 'Developed by Dongjun Choi',
                           font=base_font, background='skyblue')
        info_label.pack()
        self.info_popup.mainloop()

    def adjust_grid(self):
        self.adjust_popup = Toplevel()
        self.adjust_popup.geometry('200x80')

        adjust_label = Label(self.adjust_popup, text='Grid Interval Settings', font=base_font)
        adjust_label.pack()
        self.adjust_value = IntVar()
        self.adjust_value.set(self.d_interval)  # self.div_num -> self.d_interval
        self.entry_value = Entry(self.adjust_popup, textvariable=self.adjust_value, font=base_font)
        self.entry_value.pack()

        self.enter_button = Button(self.adjust_popup, text='Enter', command=self.adjust_grid_value)
        self.enter_button.pack()

        self.adjust_popup.bind('<Return>', self.adjust_grid_value_key)
        self.adjust_popup.mainloop()

    def adjust_grid_key(self, event):
        self.adjust_grid()

    def adjust_grid_value(self):
        try:
            if self.canvas is not None:
                if self.is_grid:
                    self.remove_grid(self.d_interval, self.dw_rest, self.dh_rest)
                    self.patches_remove()

                    self.canvas.draw()
                    self.is_grid = False
                    self.patch_array = {}
                    self.grid_button.config(text='Add Grid')

            self.d_interval = self.adjust_value.get()
            self.dw_rest, self.dh_rest = 0, 0

            self.grid_adjust_button.config(text='Grid Interval: %d' % self.d_interval)
            self.slice_check.config(text='Width: %d, Height: %d, W_adjust: %d, H_adjust: %d' %
                                         (self.ds.Columns, self.ds.Rows, self.dw_rest, self.dh_rest))

            self.patch_num = 0
            self.cond_window.config(text='%d ' % self.patch_num + self.cond_sentence(self.patch_num) + ' selected')

            self.adjust_popup.destroy()
        except:
            self.error_box('Error! Please if DICOM file exists in selected folder.')

    def adjust_grid_value_key(self, event):
        self.adjust_grid_value()

    def go_to_image(self, study_index, sop_index):
        self.folder_name = self.dcm_folder[study_index.get() - 1]

        self.dcm_list = sorted(glob.glob(self.folder_name+'/*.dcm'))
        self.slice_num = len(self.dcm_list)

        if sop_index.get() > self.slice_num:
            sop_index.set(self.slice_num)

        self.current_dcm = self.dcm_list[sop_index.get() - 1]
        self.folder_basename = os.path.basename(self.folder_name)
        self.dcm_name = os.path.basename(self.current_dcm)
        self.ds = dcm.read_file(self.current_dcm)

        self.image_array = self.ds.pixel_array

    def image_setting(self, study_index, sop_index):
        if True:
            if self.canvas is None:
                self.f1 = Figure(figsize=(self.f_size, self.f_size), dpi=self.image_dpi)
                self.ax = self.f1.add_axes((0, 0, 1, 1), frameon=True)

                self.ax.xaxis.set_visible(False)
                self.ax.yaxis.set_visible(False)

                self.ax.imshow(self.image_array, cmap='gray')

                self.canvas = FigureCanvasTkAgg(self.f1, master=self.frame13)
                self.canvas.draw()
                self.canvas.get_tk_widget().pack(side=LEFT, anchor='nw', fill='both', expand=True)

                self.gui.bind('<space>', self.slice_next_key)
                self.gui.bind('<Left>', self.study_prev_key)
                self.gui.bind('<Right>', self.study_next_key)
                self.gui.bind('<Up>', self.slice_prev_key)
                self.gui.bind('<Down>', self.slice_next_key)
                self.gui.bind('<g>', self.add_grid_key)

                self.canvas.callbacks.connect('motion_notify_event', self.motion_coord)
                self.canvas.callbacks.connect('button_press_event', self.press_mouse)

                self.canvas.callbacks.connect('button_press_event', self.adjust_location_grid)
                self.canvas.callbacks.connect('motion_notify_event', self.adjust_motion_grid)
                self.canvas.callbacks.connect('button_release_event', self.adjust_release_grid)
            else:
                self.ax.clear()
                self.ax.imshow(self.image_array, cmap='gray')

                self.canvas.draw()

            self.is_grid = False
            self.patch_reset()

            self.study_desc.config(text='Study index:  ' + str(study_index.get()) + '/' + str(self.study_num))
            self.slice_desc.config(text='Slice Index:  ' + str(sop_index.get()) + '/' + str(self.slice_num))
            self.slice_check.config(text='Width: %d, Height: %d, W_adjust: %d, H_adjust: %d' %
                                         (self.ds.Columns, self.ds.Rows, self.dw_rest, self.dh_rest))
            self.study_check.config(text=self.folder_basename+'/'+self.dcm_name)
            self.cond_window.config(text='%d patches selected' % self.patch_num)

            self.grid_adjust_button.config(text='Grid Interval: %d' % self.d_interval)

    def motion_coord(self, event):
        if event.inaxes is not None:
            self.coord_window.config(text="X: " + str(int(event.xdata)) + "   " +
                                          "Y: " + str(int(event.ydata)), font=("Helvetica", 12))
        else:
            return

    def move_button(self, function, num_type, total_type, study_or_slice):
        if self.set_dir is None:
            self.error_box('Error! Please upload folder.')
            return
        else:
            if total_type == 1:  # if only one study or only one image
                if study_or_slice == 1:  # if only one study
                    self.error_box('Study move is not active if only one study is loaded.')
                elif study_or_slice == 2:  # if only one image in study folder
                    self.error_box('Image move is not active if only one image in study is loaded.')
                else:
                    self.error_box('Error! Invalid study_or_slice value.')
            else:
                num_type.set(function(num_type.get(), total_type))
                self.go_to_image(self.study_index, self.sop_index)
                self.image_setting(self.study_index, self.sop_index)

    def index_minus(self, num, index_total):
        if num <= 0 or num > index_total:
            num = None
        max_num = index_total
        if num != 1:
            num -= 1
        else:
            num = max_num
        return num

    def index_plus(self, num, index_total):
        if num <= 0 or num > index_total:
            num = None
        max_num = index_total
        if num < max_num and num is not None:
            num += 1
        elif num == max_num:
            num = 1
        return num

    def slice_next(self):
        self.move_button(self.index_plus, self.sop_index, self.slice_num, 2)

    def slice_prev(self):
        self.move_button(self.index_minus, self.sop_index, self.slice_num, 2)

    def slice_next_key(self, event):
        self.move_button(self.index_plus, self.sop_index, self.slice_num, 2)

    def slice_prev_key(self, event):
        self.move_button(self.index_minus, self.sop_index, self.slice_num, 2)

    def study_next(self):
        self.move_button(self.index_plus, self.study_index, self.study_num, 1)

    def study_prev(self):
        self.move_button(self.index_minus, self.study_index, self.study_num, 1)

    def study_next_key(self, event):
        self.move_button(self.index_plus, self.study_index, self.study_num, 1)

    def study_prev_key(self, event):
        self.move_button(self.index_minus, self.study_index, self.study_num, 1)

    def generate_line(self, line_type, length, d_interval, d_rest):
        line_loc = d_rest
        i = 0
        while line_loc < length:
            if line_type == 'w':
                self.w_lines[i] = self.ax.axvline(line_loc, color=self.grid_color)
                self.is_patch_w[i] = False
                if i == 0:
                    self.is_patch_w[-1] = False
            elif line_type == 'h':
                self.h_lines[i] = self.ax.axhline(line_loc,  color=self.grid_color)
                self.is_patch_h[i] = False
                if i == 0:
                    self.is_patch_h[-1] = False
            i += 1
            line_loc += d_interval

    def generate_grid(self, d_interval, dw_rest, dh_rest):
        self.generate_line('w', self.ds.Columns, d_interval, dw_rest)
        self.generate_line('h', self.ds.Rows, d_interval, dh_rest)

    def grid_setting(self, is_patch_w, is_patch_h):
        for pw in range(0, len(is_patch_w)):
            for ph in range(0, len(is_patch_h)):
                self.is_patch['_'.join([str(pw-1), str(ph-1)])] = False

    def remove_line(self, line_type, length, d_interval, d_rest):
        line_loc = d_rest
        i = 0
        while line_loc < length:
            if line_type == 'w':
                self.w_lines[i].remove()

            elif line_type == 'h':
                self.h_lines[i].remove()
            i += 1
            line_loc += d_interval

    def remove_grid(self, d_interval, dw_rest, dh_rest):
        self.remove_line('w', self.ds.Columns, d_interval, dw_rest)
        self.remove_line('h', self.ds.Rows, d_interval, dh_rest)

    def add_grid(self):
        if self.d_interval >= 1:  # whether valid div_num
            if self.is_grid is False:
                if self.canvas is None:
                    self.error_box('Error! Please upload image.')
                    return
                else:
                    self.wline_num = int(self.ds.Columns / self.d_interval)
                    self.hline_num = int(self.ds.Rows / self.d_interval)

                    self.w_lines, self.h_lines = {}, {}

                    # Add grid & grid setting
                    self.generate_grid(self.d_interval, self.dw_rest, self.dh_rest)
                    self.grid_setting(self.is_patch_w, self.is_patch_h)

                    # Recognize that grid is added
                    self.is_grid = True

                    self.canvas.draw()
                    self.grid_button.config(text='Remove Grid')
            else:  # remove grid if grid exists
                self.remove_grid(self.d_interval, self.dw_rest, self.dh_rest)
                self.patches_remove()

                self.cond_window.config(text='%d ' % self.patch_num + self.cond_sentence(self.patch_num) + ' selected')
                self.canvas.draw()

                self.is_grid = False

                self.patch_reset()

                self.cond_window.config(text='%d ' % self.patch_num +
                                             self.cond_sentence(self.patch_num) + ' selected')

                #self.patch_num = 0
                #self.patch_array = {}
                #self.is_patch = {}
                #self.is_patch_w, self.is_patch_h = {}, {}
                self.grid_button.config(text='Add Grid')
        else:
            self.error_box('Error! Invalid grid interval. Please set grid interval to 1 or higher.')
            return

    def add_grid_key(self, event):
        self.add_grid()

    def adjust_location_grid(self, event):
        if event.inaxes is not None and event.button == 3:
            dw_r, dh_r = self.dw_rest, self.dh_rest

            if self.is_grid:
                check_x = abs((event.xdata - dw_r) / self.d_interval - round((event.xdata - dw_r) / self.d_interval))
                check_y = abs((event.ydata - dh_r) / self.d_interval - round((event.ydata - dh_r) / self.d_interval))

                if check_x >= 0.1 and check_y >= 0.1:
                    return
                else:

                    self.is_adjust_grid = True
                    self.patches_remove()
                    if check_x < 0.1 and check_y < 0.1:
                        self.adjust_type = 'b'
                    elif check_x < 0.1 and check_y >= 0.1:
                        self.adjust_type = 'x'
                    elif check_x >= 0.1 and check_y < 0.1:
                        self.adjust_type = 'y'
                    else:
                        return
            else:
                return
        else:
            return

    def adjust_motion_grid(self, event):
        def rest_plus(value, d_interval):
            value += 2
            if value >= d_interval:
                value = 0
            return value

        def rest_minus(value, d_interval):
            value -= 2
            if value <= 0:
                value = d_interval - 1
            return value

        if event.inaxes is not None and event.button == 3:
            if self.is_grid is True and self.is_adjust_grid is True:
                self.x_drags.append(event.xdata)
                self.y_drags.append(event.ydata)
                if len(self.x_drags) > 1 and len(self.y_drags) > 1:
                    x_direction = self.x_drags[1] - self.x_drags[0]
                    y_direction = self.y_drags[1] - self.y_drags[0]

                    if self.adjust_type == 'b':
                        self.remove_grid(self.d_interval, self.dw_rest, self.dh_rest)
                        if x_direction >= 0:
                            self.dw_rest = rest_plus(self.dw_rest, self.d_interval)
                        else:
                            self.dw_rest = rest_minus(self.dw_rest, self.d_interval)
                        if y_direction >= 0:
                            self.dh_rest = rest_plus(self.dh_rest, self.d_interval)
                        else:
                            self.dh_rest = rest_minus(self.dh_rest, self.d_interval)
                        self.generate_grid(self.d_interval, self.dw_rest, self.dh_rest)
                        self.grid_setting(self.is_patch_w, self.is_patch_h)

                    elif self.adjust_type == 'x':
                        self.remove_line('w', self.ds.Columns, self.d_interval, self.dw_rest)
                        if x_direction >= 0:
                            self.dw_rest = rest_plus(self.dw_rest, self.d_interval)
                        else:
                            self.dw_rest = rest_minus(self.dw_rest, self.d_interval)
                        self.generate_line('w', self.ds.Columns, self.d_interval, self.dw_rest)
                        self.grid_setting(self.is_patch_w, self.is_patch_h)

                    elif self.adjust_type == 'y':
                        self.remove_line('h', self.ds.Rows, self.d_interval, self.dh_rest)
                        if y_direction >= 0:
                            self.dh_rest = rest_plus(self.dh_rest, self.d_interval)
                        else:
                            self.dh_rest = rest_minus(self.dh_rest, self.d_interval)
                        self.generate_line('h', self.ds.Rows, self.d_interval, self.dh_rest)
                        self.grid_setting(self.is_patch_w, self.is_patch_h)
                    else:
                        pass

                    self.canvas.draw()
                    self.slice_check.config(text='Width: %d, Height: %d, W_adjust: %d, H_adjust: %d' %
                                                 (self.ds.Columns, self.ds.Rows, self.dw_rest, self.dh_rest))

                    if len(self.x_drags) >= 2:
                        self.x_drags.pop(0)
                    if len(self.y_drags) >= 2:
                        self.y_drags.pop(0)
        else:
            return

    def adjust_release_grid(self, event):
        if event.inaxes is not None and event.button == 3:
            if self.is_grid is True and self.is_adjust_grid is True:
                self.patch_num = 0
                self.cond_window.config(text='%d ' % self.patch_num +
                                             self.cond_sentence(self.patch_num) + ' selected')

                self.slice_check.config(text='Width: %d, Height: %d, W_adjust: %d, H_adjust: %d' %
                                             (self.ds.Columns, self.ds.Rows, self.dw_rest, self.dh_rest))
                self.is_adjust_grid = False

    def patch_reset(self):
        self.patch_array = {}  # save patch images
        self.select_patches = {}  # display checked grid area
        self.is_patch = {}  # whether check patch patch in the grid
        self.is_patch_w, self.is_patch_h = {}, {}  # whether check patch in the grid
        self.patch_num = 0  # the number of patches checked in the image

    def press_mouse(self, event):
        def fine_adjustment(value, threshold, direction):
            if value >= threshold:
                if direction == 0:
                    pass
                else:
                    value = threshold - 2
            return value

        if event.inaxes is not None and event.button == 1:
            if self.is_grid:

                press_x = int((event.xdata - self.dw_rest) // self.d_interval)
                press_y = int((event.ydata - self.dh_rest) // self.d_interval)
                self.grid_select.config(text='Area X range: %d, Y range: %d' % (press_x+1, press_y+1))

                patch_idx = str(press_x) + '_' + str(press_y)

                if self.is_patch[patch_idx] is False:  # select patch
                    y_top = max(0, round(press_y * self.d_interval) + self.dh_rest)
                    y_bottom = min(round((press_y + 1) * self.d_interval) + self.dh_rest, self.ds.Rows)

                    x_left = max(0, round(press_x * self.d_interval) + self.dw_rest)
                    x_right = min(round((press_x + 1) * self.d_interval) + self.dw_rest, self.ds.Columns)

                    self.patch_image = self.image_array[y_top:y_bottom, x_left:x_right]

                    x_right_value = fine_adjustment(x_right, self.ds.Columns, 1)
                    y_bottom_value = fine_adjustment(y_bottom, self.ds.Rows, 1)

                    self.select_patches[patch_idx] = {}
                    self.select_patches[patch_idx]['left'] = \
                        self.ax.axvline(x=x_left,
                                        ymin=1 - (y_top / self.ds.Rows),
                                        ymax=1 - (y_bottom_value / self.ds.Rows),
                                        color=self.patch_color, linewidth=2.5)

                    self.select_patches[patch_idx]['right'] = \
                        self.ax.axvline(x=x_right_value,
                                        ymin= 1 - (y_top / self.ds.Rows),
                                        ymax= 1 - (y_bottom_value / self.ds.Rows),
                                        color=self.patch_color, linewidth=2.5)

                    self.select_patches[patch_idx]['top'] = \
                        self.ax.axhline(y=y_top,
                                        xmin=x_left / self.ds.Columns,
                                        xmax=x_right_value / self.ds.Columns,
                                        color=self.patch_color, linewidth=2.5)

                    self.select_patches[patch_idx]['bottom'] = \
                        self.ax.axhline(y=y_bottom_value,
                                        xmin=x_left / self.ds.Columns,
                                        xmax=x_right_value / self.ds.Columns,
                                        color=self.patch_color, linewidth=2.5)

                    self.canvas.draw()
                    self.is_patch[patch_idx] = True
                    self.patch_array[patch_idx] = self.patch_image
                    self.patch_num += 1

                    self.cond_window.config(text='%d '%self.patch_num +
                                                 self.cond_sentence(self.patch_num)+' selected')

                else:  # remove patch
                    self.patch_remove(patch_idx)
                    self.canvas.draw()
                    self.patch_num -= 1

                    self.cond_window.config(text='%d ' % self.patch_num +
                                                 self.cond_sentence(self.patch_num)+' selected')

            else:
                self.error_box('Error! Please click to add the grid first.')

    def patch_remove(self, patch_idx):
        self.select_patches[patch_idx]['left'].remove()
        self.select_patches[patch_idx]['right'].remove()
        self.select_patches[patch_idx]['top'].remove()
        self.select_patches[patch_idx]['bottom'].remove()
        self.is_patch[patch_idx] = False
        self.patch_array[patch_idx] = None

    def patches_remove(self):  # remove patches keeping grid
        for pw in range(0, len(self.is_patch_w)):
            for ph in range(0, len(self.is_patch_h)):
                patch_idx = '_'.join([str(pw - 1), str(ph - 1)])
                if self.is_patch[patch_idx]:
                    self.patch_remove(patch_idx)  # remove patch area
                    self.is_patch[patch_idx] = False

    def cond_sentence(self, patch_num):
        if patch_num == 1:
            num_count = 'patch'
        else:
            num_count = 'patches'
        return num_count

    def write_dcm(self, pixel_array, pw, ph, filename):
        read_meta = dcm.filereader.read_file_meta_info(self.current_dcm)

        file_meta = Dataset()
        file_meta.MediaStorageSOPClassUID = 'MR patch image storage'
        file_meta.MediaStorageSOPInstanceUID = read_meta.MediaStorageSOPInstanceUID
        file_meta.ImplementationClassUID = read_meta.ImplementationClassUID

        ds = FileDataset(filename, {}, file_meta=file_meta, preamble=b'\x00'*128)

        ds.file_meta.TransferSyntaxUID = dcm.uid.ImplicitVRLittleEndian
        ds.Modality = 'MR'
        ds.ContentDate = str(datetime.date.today()).replace('-', '')
        ds.ContentTime = str(time.time())

        ds.StudyInstanceUID = self.dcm_tag('StudyInstanceUID')
        ds.SeriesInstanceUID = self.dcm_tag('SeriesInstanceUID')+'001'
        ds.SOPClassUID = self.dcm_tag('SOPClassUID') + '%03d' % pw + '%03d' % ph
        ds.SOPInstanceUID = self.dcm_tag('SOPInstanceUID') + '%03d' % pw+'%03d' % ph

        ds.SecondaryCaptureDeviceManufactur = 'Python 3.6.0'

        ds.StudyID = self.dcm_tag('StudyID')
        ds.SeriesNumber = self.dcm_tag('SeriesNumber')
        ds.AcquisitionNumber = self.dcm_tag('AcquisitionNumber')
        ds.InstanceNumber = self.dcm_tag('InstanceNumber')
        ds.StudyDescription = 'MR patch study'
        ds.SeriesDescription = 'MR patch series'

        ds.PatientName = self.dcm_tag('PatientName')
        ds.PatientID = self.dcm_tag('PatientID')
        ds.PatientSex = self.dcm_tag('PatientSex')
        ds.PatientAge = self.dcm_tag('PatientAge')
        ds.PatientWeight = self.dcm_tag('PatientWeight')

        ds.SamplesPerPixel = 1
        ds.PhotometricInterpretation = 'MONOCHROME2'
        ds.PixelRepresentation = 0

        ds.HighBit = self.dcm_tag('HighBit')
        ds.BitsStored = self.dcm_tag('BitsStored')
        ds.BitsAllocated = self.dcm_tag('BitsAllocated')

        ds.SmallestImagePixelValue = '\\x00\\x00'.encode()
        ds.LargestImagePixelValue = '\\xff\\xff'.encode()
        ds.Columns = pixel_array.shape[1]
        ds.Rows = pixel_array.shape[0]
        if pixel_array.dtype != np.uint16:
            pixel_array = pixel_array.astype(np.uint16)
        ds.PixelData = pixel_array.tostring()

        ds.save_as(filename)
        return

    def dcm_tag(self, attribute):
        if attribute in dir(self.ds):
            dcm_tag = getattr(self.ds, attribute)
        else:
            dcm_tag = ''
        return dcm_tag

    def error_box(self, error_text):
        self.error_popup = Toplevel()
        self.error_popup.geometry('700x30')
        error_label = Label(self.error_popup, text=error_text, font=('Helvetica', 15),
                            background="snow")
        error_label.pack()
        self.error_popup.mainloop()


viewer = ViewerMRI()
viewer.gui.mainloop()



